{-# LANGUAGE OverloadedStrings #-}

module Main where

import Lib
import Helpers (loadProg, evalProg)
import Term (showProg)
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
import System.Environment


prog :: G.Program
prog =  G.Program [] [G.Def (G.NM {G.unNM="grinMain"}) [] (G.SApp (G.NM {G.unNM = "fun"}) [(G.Var (G.NM {G.unNM = "arg"}))])] 

main :: IO ()
main = do
    [path] <- getArgs
    p <- loadProg [path] [] [] Nothing
    case p of
        Nothing -> putStrLn ""
        Just p' -> do
            let (poitin, grin) = transformP p'
            putStrLn . showProg $ poitin
            printGrin grin
            (res, _) <- evalProgram IOReducer grin
            print res

