module Vl.Process where
import Control.Algebra
import Control.Carrier.Reader qualified as C
import Control.Carrier.State.Strict qualified as C
import Control.Effect.Error qualified as C
import Control.Effect.Fresh qualified as C
import Control.Effect.Lift qualified as C

import Error.Diagnose

import Prettyprinter

import Relude

import Utils.Pretty

import Vl.Check
import Vl.Common
import Vl.Defs
import Vl.Error
import Vl.Expr
import Vl.Jesper (buildPatternFunc)
import Vl.Lens
import Vl.Name
import Vl.Parser as Parser
import Vl.SourceStore
import Vl.TT
import Vl.Value

type HasProcess sig m =
  ( Has (C.Lift IO) sig m
  , GenUUID sig m
  , HasError sig m
  , WithDefs sig m
  , WithSourceStore sig m
  )

type HasProcessDef sig m =
  ( HasProcess sig m
  , GotNamespacing sig m
  )

checkInProcess :: HasProcessDef sig m => C.StateC CheckSt (C.ReaderC Context (C.ReaderC CheckMode m)) a -> m a
checkInProcess = C.runReader CheckModeExpr . C.runReader emptyContext . C.evalState initCheckSt

checkInProcess' :: HasProcessDef sig m => C.StateC CheckSt (C.ReaderC CheckMode m) a -> m a
checkInProcess' = C.runReader CheckModeExpr . C.evalState initCheckSt


processClaim :: HasProcessDef sig m => EClaim -> m ()
processClaim (EClaim range name namerange ty) = do
  qname <- makeQNameSingleton name
  ty <- checkInProcess $ checkTypeExpr ty
  addNewDef namerange qname ty DefClaim


processData :: forall sig m. HasProcessDef sig m => EData -> m ()
processData (EData tycon inhabit) = do
  tycqname <- makeQNameSingleton (tycon^.name)
  checkTyCon tycqname
  underNamespace (tycon^.name) do
    checkInhabit tycqname
  where
  makeDtConName :: QName -> Name -> QName
  makeDtConName tycqname@(QName ns n) dtcname = QName (ns `snoc` n) dtcname

  checkTyCon :: QName -> m ()
  checkTyCon tycqname = do
    ty <- checkInProcess $ checkTypeExpr (tycon^.dtype)
    addNewDef (tycon^.nameRange) tycqname ty $ DefTypeCon TypeCon
      { _inhabit = case inhabit of
        EInhabit_External      -> Inhabit_External
        EInhabit_DataCons cons -> Inhabit_DataCons (cons^..traverse.name.to (makeDtConName tycqname))
      }

  checkDtCon :: QName -> EConstructor -> m ()
  checkDtCon tycqname dtcon = do
    let qname = makeDtConName tycqname (dtcon^.name)
    ty <- checkInProcess $ checkTypeExpr (dtcon^.dtype)
    addNewDef (dtcon^.nameRange) qname ty DefDataCon

  checkInhabit :: QName -> m ()
  checkInhabit tycqname = do
    case inhabit of
      EInhabit_External        -> pass
      EInhabit_DataCons dtcons -> traverse_ (checkDtCon tycqname) dtcons


processClauses :: HasProcessDef sig m => Range -> QName -> NonEmpty EClause -> m ()
processClauses fnnamerange fnqname clauses = do
  d <- lookupDefSured fnqname
  clauses <- checkInProcess $ traverse (checkClause Infer ClauseModePM) clauses
  -- C.sendIO $ putDocLn $ "processClauses" <+> afunc (pretty fnname) <> ", begin buildPatternFunc"
  func <- C.runReader emptyContext $ buildPatternFunc fnqname (d^.dtype) clauses
  updateDef fnqname (info .~ DefPM func)
  -- C.throwError $ GenericReport $ Err Nothing "no corresponding claim"
  --   [ (toPos (head clauses^.range), This $ "no corresponding claim '" <> show fnname <> "'")
  --   ]
  --   []


processStructBase :: HasProcessDef sig m => PiInfo -> Name -> EStructBase -> m ()
processStructBase objpiinfo objname struct = C.runReader emptyContext do
  underTyCon $ \tycqname dtcqname -> do
    withImplicitParams $ do
      (dtcargnames, dtcobjty, objty) <- checkDtCon tycqname dtcqname -- the end type of the telescope is kinda awkward, but it doesn't matter
      -- gamma <- contextGammaNames <$> currentContext
      -- C.sendIO $ putDocLn $ "objty" <+> "=" <+> renderTerm gamma objty
      underParam (Param objpiinfo objname objty) do
        tele <- defsEval $ weakenBy objname dtcobjty
        makeProjections dtcqname dtcargnames (struct^.dtcParams) tele
  where
  makeProjections :: (GotContext sig m, HasProcessDef sig m) => QName -> ArgNames -> [EParam] -> Type' NF -> m ()
  makeProjections dtcqname dtcargnames [] objty = pass
  makeProjections dtcqname dtcargnames (eparam : eparams) (NPi (Param _ projpiinfo projdestty) nextparams) = do
    ctx <- currentContext
    pmname <- makeQNameSingleton (eparam^.name)
    let
      projty = abstractPis (quotate projdestty) ctx
      var = length eparams
      pmargnames = reverse (contextGammaNames ctx)
      pm = PatternFunc pmargnames
        $ CaseOn 0 $ fromCaseArmList
          [ CaseDtCon dtcqname dtcargnames (CaseScope (Var var))
          ]
    -- C.sendIO $ putDocLn $ afunc (pretty (eparam^.name)) <+> asymbol ":" <+> renderTerm (contextGammaNames ctx) projty
    -- C.sendIO $ putDocLn $ renderPatternFunc (eparam^.name) pm
    addNewDef (eparam^.nameRange) pmname projty (DefPM pm)

    let projtm = foldSpine (Func pmname) (constArgs (levelOf ctx))
    projtm <- defsEval projtm
    makeProjections dtcqname dtcargnames eparams (runScope nextparams projtm)
  makeProjections dtcqname dtcargnames (eparam : eparams) objty = error "bad type"

  checkDtCon tycqname dtcqname = do
    let objty = foldSpine (Con TyCon tycqname) (constArgs (length (struct^.tycParams)))
    (dtcargnames, dtcobjty) <- underParams (struct^.dtcParams) do
      dtcctx <- currentContext
      let dtcargnames = reverse (contextGammaNames dtcctx)
      let objctx = contextSub (length (struct^.dtcParams)) dtcctx
      let dtcobjty = abstractPis (weakenBy objctx objty) objctx
      pure (dtcargnames, dtcobjty)
    dtcty <- abstractPis dtcobjty <$> currentContext
    addNewDef (struct^.dtcNameRange) dtcqname dtcty DefDataCon
    pure (dtcargnames, dtcobjty, objty)

  underTyCon :: (GotContext sig m, HasProcessDef sig m) => (QName -> QName -> m a) -> m a
  underTyCon act = do
    underParams (struct^.tycParams) do
      tycqname <- makeQNameSingleton (struct^.tycName)
      underNamespace (struct^.tycName) do
        dtcqname <- makeQNameSingleton (struct^.dtcName)
        tycty <- abstractPis TType <$> currentContext
        addNewDef (struct^.tycNameRange) tycqname tycty
          (DefTypeCon (TypeCon (Inhabit_DataCons [dtcqname])))
        act tycqname dtcqname

  underParams :: (GotContext sig m, HasProcessDef sig m) => [EParam] -> m a -> m a
  underParams [] act = act
  underParams (param : params) act = do
    param <- checkInProcess' $ checkParam param
    underParam param $ underParams params $ act

  withImplicitParams :: GotContext sig m => m a -> m a
  withImplicitParams = C.local @Context
    (traverse . piInfo %~ \case
      Explicit     -> Implicit IsImplicit
      Implicit imp -> Implicit imp
    )


processFixity :: HasProcessDef sig m => EFixity -> m ()
processFixity EFixity{..} = do
  (n, _) <- resolveAmbigNameUniquely _nameRange _name
  updateDef n (opInfo .~ _opInfo)


processInstance :: HasProcessDef sig m => EInstance -> m ()
processInstance EInstance{..} = do
  (n, _) <- resolveAmbigNameUniquely _nameRange _name
  C.modify @Defs $ searchHints . instances %~ (n :)


processNamespace :: HasProcessDef sig m => ENamespace -> m ()
processNamespace ENamespace{..} = do
  underNamespace _name $ processDefs _defs


processDefs :: forall sig m. HasProcessDef sig m => [EDef] -> m ()
processDefs [] = pass
processDefs (EDefStruct struct : ds) =
  processStructBase Explicit (UserName "obj") struct *> processDefs ds
processDefs (EDefInterface iface : ds) =
  processStructBase (Implicit IsInstance) (UserName "impl") iface *> processDefs ds
processDefs (EDefFixity fixity : ds) =
  processFixity fixity *> processDefs ds
processDefs (EDefInstance inst : ds) =
  processInstance inst *> processDefs ds
processDefs (EDefClaim claim : ds) =
  processClaim claim *> processDefs ds
processDefs (EDefData data' : ds) =
  processData data' *> processDefs ds
processDefs (EDefNamespace namespace : ds) =
  processNamespace namespace *> processDefs ds
processDefs (EDefClause firstclause : ds) = do
  (firstclause, (fnnamerange, fnqname)) <- checkLHSFuncName firstclause
  (restclauses, ds) <- collect fnqname ds
  processClauses fnnamerange fnqname (firstclause :| restclauses)
  processDefs ds
  where
  collect :: QName -> [EDef] -> m ([EClause], [EDef])
  collect fnqname (EDefClause clause : ds) = do
    -- NOTE: even if that's just the ambiguous names being the same, its enough to group them together
    (clause, (_, fnqname')) <- checkLHSFuncName clause
    if fnqname == fnqname'
      then first (clause :) <$> collect fnqname ds
      else pure ([], EDefClause clause : ds)
  collect fnqname ds = pure ([], ds)

  checkLHSFuncName :: EClause -> m (EClause, (Range, QName))
  checkLHSFuncName clause = do
    lhs' <- checkFixity (clause^.lhs)
    clause <- pure $ clause & lhs .~ lhs'
    (lhs', (fnrange, fnqname)) <- getFuncAmbigName lhs'
    pure (clause&lhs.~lhs', (fnrange, fnqname))

  getFuncAmbigName :: Expr -> m (Expr, (Range, QName))
  getFuncAmbigName (EApp apprange f x)  = do
    (f, r) <- getFuncAmbigName f
    pure (EApp apprange f x, r)
  getFuncAmbigName (EVar varrange ambigname) = do
    (qname, _) <- resolveAmbigNameUniquely varrange ambigname
    pure (EResolvedVar varrange qname, (varrange, qname))
  getFuncAmbigName (EResolvedVar varrange qname) = do
    pure (EResolvedVar varrange qname, (varrange, qname))
  getFuncAmbigName expr = do
    -- expr is an illegal LHS expression
    C.throwError $ GenericReport $ Err Nothing "Illegal LHS expression"
      [ (toPos $ exprRange expr, This "illegal LHS expression")
      ]
      []

processFile :: HasProcess sig m => EFile -> m ()
processFile (EFile defs) = C.runReader @Namespacing initFileNamspacing $ processDefs defs


handleParsing :: HasProcess sig m => Either (Diagnostic Text) a -> m a
handleParsing = either (C.throwError . GenericDiagnostic) pure

loadVirtExpr :: HasProcess sig m => Text -> m (Term, Type' Term)
loadVirtExpr src = do
  origin <- FromVirt "expr" <$> C.fresh
  registerSource origin src
  expr <- handleParsing $ runWrappedParser @Text userExpression origin src
  C.sendIO $ putDocLn $ "loadVirtExpr: " <> show expr
  C.runReader initEmptyNamespacing $ checkInProcess $ checkExpr expr Infer

loadVirtFile :: HasProcess sig m => Text -> m ()
loadVirtFile src = do
  origin <- FromVirt "file" <$> C.fresh
  registerSource origin src
  file <- handleParsing $ runWrappedParser @Text Parser.userFile origin src
  processFile file

loadFile :: HasProcess sig m => FilePath -> m ()
loadFile path = do
  let origin = FromFile (fromString path)
  src <- decodeUtf8 <$> C.sendIO (readFileBS path)
  registerSource origin src
  file <- handleParsing $ runWrappedParser @Text Parser.userFile origin src
  processFile file
