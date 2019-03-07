{-# LANGUAGE GADTs #-}

import           Dhall.Typed
import           Dhall.Typed.Context
import           Dhall.Typed.Core
import qualified Data.Text.IO                          as T
import qualified Data.Text.Prettyprint.Doc.Render.Text as PP
import qualified Dhall                                 as D
import qualified Dhall.Core                            as D
import qualified Dhall.Pretty                          as D

main :: IO ()
main = do
    res <- fmap D.denote . D.inputExpr =<< T.getContents
    case toTyped CtxNil res of
      Left e              -> print e
      Right (SomeDExpr x) -> PP.putDoc . D.prettyExpr . fromTyped $ x
