module Main where

import Lib
import Helpers (loadProg)
import Term (showProg)


main :: IO ()
main = do
    p <- loadProg ["example"] [] [] Nothing
    putStrLn "Hello World"

