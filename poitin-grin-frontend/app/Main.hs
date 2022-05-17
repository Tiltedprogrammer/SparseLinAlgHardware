{-# LANGUAGE OverloadedStrings #-}

module Main where

import Helpers (loadProg, evalProg)
import Term
import Data.Maybe (fromMaybe, isJust)
import Control.Monad
import qualified Grin.Grin as G
import Grin.Pretty
import Transformations.Transformations
import qualified Data.Text.IO as Text
import qualified Text.Megaparsec as M
import qualified Text.Megaparsec.Char as M
import Grin.Parse

import Pipeline.Eval
import Reducer.Pure
import Reducer.PrimOps
import Pipeline.Pipeline
import System.Environment



opts = defaultOpts
                    { _poOutputDir = ".grin-output"
                    , _poFailOnLint = False
                    , _poLogging = False
                    , _poSaveBinary = False
                    , _poCFiles = []
                    }

steps = [ InlineEval
  , SparseCaseOptimisation
  , SimpleDeadFunctionElimination
  , SimpleDeadParameterElimination
  , SimpleDeadVariableElimination
  , EvaluatedCaseElimination
  , TrivialCaseElimination
  , UpdateElimination
  , NonSharedElimination
  , CopyPropagation
  , ConstantPropagation
  , CommonSubExpressionElimination
  , CaseCopyPropagation
  , CaseHoisting
  , GeneralizedUnboxing
  , ArityRaising
  , InlineApply
  , LateInlining
  ]


optimizeGrin prog = optimizeWith opts prog [] steps [SaveGrin (Rel $ _poOutputDir opts)]
evalGrin = evalProgram  (PureReducer (EvalPlugin evalPrimOp))


main :: IO ()
main = do
    [path] <- getArgs
    p <- loadProg [path] [] [] Nothing
    case p of
        Nothing -> putStrLn ""
        Just (p') -> do
            let (poitin, grin) = transformP p'
            
            optGrin <- optimizeGrin grin
            (res, _) <- evalGrin optGrin
            printGrin grin
            print res

