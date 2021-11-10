module Main where

import Lib
import Helpers (loadProg, evalProg)
import Term (showProg)
import Data.Maybe (fromMaybe, isJust)
import Control.Monad
import qualified Grin.Grin as G
import Transformations.Transformations


main :: IO ()
main = do
    p <- loadProg ["map"] [] [] Nothing
    case p of
        Nothing -> putStrLn ""
        Just p' -> do
            let (t,d) = unifyNames p'
            putStrLn $ showProg (t,d)
            (v, r, a) <- evalProg (free t) t d
            print v
            putStrLn ("Reductions: " ++ show r)
            putStrLn ("Allocations: " ++ show a)



        -- putStrLn unifyNames

