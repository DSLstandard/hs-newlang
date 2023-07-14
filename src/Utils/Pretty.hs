module Utils.Pretty where

import Prettyprinter
import Prettyprinter.Render.Terminal

import Relude

putDocLn :: MonadIO m => Doc AnsiStyle -> m ()
putDocLn x = liftIO do
  putDoc x
  putStrLn ""

separatedBy :: Doc ann -> [Doc ann] -> Doc ann
separatedBy sep = hcat . punctuate sep
