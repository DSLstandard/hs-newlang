module Main where

import Control.Carrier.Error.Either qualified as C
import Control.Carrier.Fresh.Strict qualified as C
import Control.Carrier.Reader qualified as C
import Control.Carrier.State.IORef qualified as C
import Control.Effect.Lift qualified as C

import Error.Diagnose

import NeatInterpolation

import Prettyprinter
import Prettyprinter.Render.Terminal

import Relude

import Utils.Pretty

import Vl.Check
import Vl.Common
import Vl.Defs
import Vl.Error
import Vl.Expr
import Vl.Interpret
import Vl.Lens
import Vl.Name
import Vl.Parser
import Vl.Process
import Vl.SourceStore
import Vl.TT
import Vl.Unify
import Vl.Value


seeUserHole :: HasProcess sig m => QName -> m ()
seeUserHole qname = do
  definfo <- lookupDefSuredAs _DefUserHole qname
  ty <- defsNormWith optsReduceMetas (definfo^.dtype)
  (ctx, localty) <- C.runReader emptyContext $ underTelescope ty \_ localty -> do
    ctx <- currentContext
    pure (ctx, localty)
  let localtydoc = pad <> afunc ("?" <> pretty qname) <+> asymbol ":" <+> renderTerm (contextGammaNames ctx) localty
  paramdocs <- renderParams ctx
  C.sendIO $ putDocLn $ vsep (reverse (localtydoc : br : paramdocs))
  where
  br = aspecial "------------------------------"
  pad = aspecial ">" <> " "

  renderParams :: HasProcess sig m => Context -> m [Doc AnsiStyle]
  renderParams [] = pure []
  renderParams (param : ctx) = do
    param <- traverse (defsNormWith optsReduceAll) param
    let paramdoc = renderParam (contextGammaNames ctx) param
    paramdocs <- renderParams ctx
    pure $ (pad <> paramdoc) : paramdocs


testExpr :: HasProcess sig m => Text -> m ()
testExpr src = do
  (x, t) <- loadVirtExpr src
  -- seeUserHole (UserName "a")
  C.sendIO $ putDocLn $ aspecial "old:" <+> renderTerm [] x <+> asymbol ":" <+> renderTerm [] t
  x <- defsNormWith optsReduceMetas x
  t <- defsNormWith optsReduceMetas t
  C.sendIO $ putDocLn $ aspecial "mid:" <+> renderTerm [] x <+> asymbol ":" <+> renderTerm [] t
  x <- defsNormWith optsReduceAll x
  t <- defsNormWith optsReduceAll t
  C.sendIO $ putDocLn $ aspecial "new:" <+> renderTerm [] x <+> asymbol ":" <+> renderTerm [] t


vmain :: HasProcess sig m => m ()
vmain = do
  loadFile "scripts/common.vl"
  loadFile "scripts/test_practical.vl"
  C.sendIO $ putDocLn $ aspecial "done loading files"
  -- testExpr "main"
  guessnames <- C.gets @Defs $ view guessNames
  C.sendIO $ putDocLn $ "UNSOLVED GUESSES: " <> pretty (toList guessnames)
  -- (x, t) <- loadVirtExpr "forever (putl_str stdout \"hello world!!!!\")"
  -- (x, t) <- loadVirtExpr "putl_str stdout \"hello world\""
  -- testExpr "show (Some False)"
  -- (x, t) <- loadVirtExpr "guessingGame"
  -- C.sendIO $ putDocLn $ aspecial "interpreting..."
  -- C.sendIO $ putDocLn $ "UNSOLVED GUESSES: " <> pretty (toList guessnames)
  -- seeUserHole "a"
  -- defs <- C.get @Defs
  -- C.sendIO $ interpret defs x
  pass

-- | Testing namespaces
vmain2 :: HasProcess sig m => m ()
vmain2 = do
  loadFile "scripts/common.vl"
  loadFile "scripts/test_namespace.vl"

tmain :: HasProcess sig m => m ()
tmain = do
  let gamma = [UserName "c", UserName "b", UserName "a", UserName "k"]
  let lhs :: Term = foldSpine (Meta "alpha") [Var 1]
  -- let rhs = foldSpine (Var 1) [Lam (UserName "x") (foldSpine (Var 2) [Var 0])]
  let rhs :: Term = Lam (UserName "x") (foldSpine (Var 2) [Var 0])
  -- let lvl = length gamma
  -- let h1 = foldSpine (Meta (UserName "H1")) [Var 3, Var 0, Var 2]
  -- let h2 = foldSpine (Meta (UserName "H2")) [Var 3, Var 2]
  -- let bruh = Param Explicit (UserName "f") TType
  -- let lhs = Pi bruh $ Pi (Param Explicit boringName h1) (weaken 1 h2)
  -- let rhs = Pi bruh $ Pi (Param Explicit boringName (Var 0)) (Var 3)
  C.sendIO $ putDocLn $ renderTerm gamma lhs <+> asymbol "~" <+> renderTerm gamma rhs
  lhs <- defsNormWith optsReduceAll lhs
  rhs <- defsNormWith optsReduceAll rhs
  C.sendIO $ putDocLn $ renderTerm gamma lhs <+> asymbol "~" <+> renderTerm gamma rhs
  lhsnf <- defsEval lhs
  rhsnf <- defsEval rhs
  let a = runUnify (UnifyEnv (const Nothing)) $ levelUnifyNF gamma 0 lhsnf rhsnf
  case a of
    Nothing -> C.sendIO $ putDocLn "cannot unify"
    Just ((), res) -> do
      C.sendIO $ putDocLn $ nest 2 $ vsep ["result:", renderUResult res]

main :: IO ()
main = do
  void
    $ C.evalState emptyDefs
    $ C.evalState emptySourceStore
    $ C.evalFresh 0
    $ C.runError @Error
    $ do
      C.catchError @Error vmain
        $ \err -> do
          diag <- addFilesToDiagnostic $ errorToDiagnostic err
          printDiagnostic stderr True True 2 defaultStyle diag
