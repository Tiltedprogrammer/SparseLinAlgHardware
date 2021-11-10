{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}

module Transformations.Transformations(module Control.Monad.State,
                                       module Term,
                                       module Transformations.Transformations) where

import Term
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Debug.Trace



data Env = Env {defs :: Map.Map String ([String],Term),
                freeVars :: Set.Set String,
                uniqueSupplier :: [String]
                }

-- here we just rename all let bindings so they introduce only new variable names (though they are not used explicitly due to de-brujin indexes)


runPass :: (Term -> State Env Term) -> State Env ()
runPass pass = do
    Env {defs, freeVars, uniqueSupplier} <- get
    t' <- mapM_
        (\x@(name, (args, body)) -> do
            t <- pass body

            Env {defs, freeVars, uniqueSupplier} <- get
            put (Env {defs=Map.insert name (args, t) defs, freeVars=freeVars,uniqueSupplier=uniqueSupplier})

            return ()) (Map.toList defs)
    return ()

unifyNames :: Prog -> Prog
unifyNames p@(main', defs') = let
                                  supplier = [replicate k ['a'..'z'] | k <- [1..]] >>= sequence
                                  freeVars' = Set.fromList ("main" : map (\x@(name,(args,body)) -> name) defs')
                                  defs'' = (("main", ([], main')) : defs')
                                  env = Env {defs = Map.fromList defs'', freeVars = freeVars', uniqueSupplier = supplier }

                                  (_, defs''') = runState (runPass unifyNamesHelper >> runPass variableLift) env

                                  -- unify
                                --   (_, defs''') = runState (do
                                --       Env {defs, freeVars, uniqueSupplier} <- get
                                --       mapM_ (\x@(name, (args, body)) -> do
                                --           t <- unifyNamesHelper body

                                --           Env {defs, freeVars, uniqueSupplier} <- get
                                --           put (Env {defs=Map.insert name (args, t) defs, freeVars=freeVars,uniqueSupplier=uniqueSupplier})

                                --           return ()
                                --           ) (Map.toList defs)
                                --       ) env
                                  Just (_, main) = Map.lookup "main" (defs defs''')
                                  rest = Map.toList $ Map.delete "main" (defs defs''') in

                                      (main, rest) where


                                --   state = mapM (\x@(name, (args,t)) -> unifyNamesHelper t) defs'' :: State Env [Term]
                                --   (result@(r:rs), s) = runState state env
                                --   (result1@(r1:rs1), s1) = runState (mapM variableLift result) s
                                --   (r2, s2) = runState (lambdaLift r1 0) s1 in

                                --     (r2, zipWith (\l@(name, (args, t)) r -> (name, (args, r))) defs' (tail $ defs s2)) where

    unifyNamesHelper :: Term -> State Env Term
    unifyNamesHelper t = do
        Env {defs, freeVars, uniqueSupplier} <- get

        case t of
            Lambda s t' -> do
                t'' <- unifyNamesHelper t'
                return (Lambda s t'')
            Con s args@(x:xs) -> do
                Con s <$> mapM unifyNamesHelper args
            Apply t1 t2 -> do
                t1' <- unifyNamesHelper t1
                t2' <- unifyNamesHelper t2
                return (Apply t1' t2')
            Case t' l@(x:xs) -> do
                scrut <- unifyNamesHelper t'
                branches <- mapM (\x@(name,args,t'') -> unifyNamesHelper t'') l
                return $ Case scrut (zipWith (\x@(name, args, _) y -> (name,args,y)) l branches)
            Let name t1 t2 -> do

                -- if name `Set.member` freeVars then do
                --     let (prefix, end) = span (\x -> (name ++ "_" ++ x) `Set.member` freeVars) uniqueSupplier
                --         (x:xs) = end in do
                --                 put (Env {defs = defs, freeVars = Set.insert (name ++ "_" ++ x) freeVars, uniqueSupplier=xs})
                --                 t1' <- unifyNamesHelper t1
                --                 t2' <- unifyNamesHelper t2
                --                 return $ Let (name ++ "_" ++ x) t1' t2'
                -- else do
                --     put (Env {defs = defs, freeVars = Set.insert name freeVars, uniqueSupplier=uniqueSupplier})
                --     t1' <- unifyNamesHelper t1
                --     t2' <- unifyNamesHelper t2
                --     return (Let name t1' t2')
                let (name', uniqueSupplier') = getNewName name freeVars uniqueSupplier

                put (Env {defs = defs, freeVars = Set.insert name' freeVars, uniqueSupplier = uniqueSupplier'})
                t1' <- unifyNamesHelper t1
                t2' <- unifyNamesHelper t2
                return (Let name' t1' t2')

            Unfold {} -> error "Unexpected unfold" -- replace with StateT

            Fold {} -> error "Unexpected fold" -- same here

            x -> return x

getNewName :: String -> Set.Set String -> [String] -> (String, [String])
getNewName name freeVars supplier = if name `Set.member` freeVars then
                                        let (prefix, end) = span (\x -> (name ++ "_" ++ x) `Set.member` freeVars) supplier
                                            (x:xs) = end in
                                                (name ++ "_" ++ x, xs)
                                    else
                                            (name, supplier)


variableLift :: Term -> State Env Term
variableLift t = do
            Env {defs, freeVars, uniqueSupplier} <- get
            case t of

                Apply t1 t2 -> do
                   let (name1, uniqueSupplier1) = getNewName "var" freeVars uniqueSupplier
                   put (Env {defs = defs, freeVars = Set.insert name1 freeVars, uniqueSupplier = uniqueSupplier1})

                   t1' <- variableLift t1

                   Env {defs, freeVars, uniqueSupplier} <- get

                   let (name2, uniqueSupplier2) = getNewName "var" freeVars uniqueSupplier
                   put (Env {defs = defs, freeVars = Set.insert name2 freeVars, uniqueSupplier = uniqueSupplier2})

                   t2' <- shift 1 <$> variableLift t2


                   return (Let name1 t1' (Let name2 t2' (Apply (Bound 1) (Bound 0))))
                Lambda name body -> do
                   let (name1, uniqueSupplier1) = getNewName "var" freeVars uniqueSupplier
                   put (Env {defs = defs, freeVars = Set.insert name1 freeVars, uniqueSupplier = uniqueSupplier1})

                   body' <- variableLift body

                   return (Let name1 (Lambda name body') (Bound 0))
               -- each con's parameter should be a variable
                Con c ts -> do
                   ts' <- mapM variableLift ts
                   let binds = reverse [Bound i | i <- [0 .. length ts' - 1]]
                   names' <- sequence [(\(t', i) -> do
                           Env {defs, freeVars, uniqueSupplier} <- get

                           let (name', uniqueSupplier') = getNewName "var" freeVars uniqueSupplier

                           put (Env {defs = defs, freeVars = Set.insert name' freeVars, uniqueSupplier = uniqueSupplier'})

                           return (Let name' (shift i t'))) t' | t' <- zip ts' [0 .. length ts' - 1]]

                   return $ foldr ($) (Con c binds) names'
                Case t' branches -> do
                    let (name', uniqueSupplier') = getNewName "var" freeVars uniqueSupplier
                    put (Env {defs = defs, freeVars = Set.insert name' freeVars, uniqueSupplier = uniqueSupplier'})

                    t1' <- variableLift t'

                    branches' <- mapM (\x@(name,args,t'') -> variableLift (shift 1 t'')) branches
                    return $ Let name' t1' (Case (Bound 0) (zipWith (\x@(name, args, _) y -> (name,args,y)) branches branches'))

                Let name t1@(Free _) t2 -> do
                    t2' <- variableLift t2
                    return (Let name t1 t2')

                Let name t1@(Bound _) t2 -> do
                    t2' <- variableLift t2
                    return (Let name t1 t2')
                Let name t1@(Fun _) t2 -> do
                    t2' <- variableLift t2
                    return (Let name t1 t2')
                Let name t1 t2 -> do
                    t1' <- variableLift t1
                    t2' <- variableLift t2
                    return (Let name t1' t2')
                Unfold {} -> error "unexpected Unfold"
                Fold {} -> error "exexpectef Fold"

                x -> return x

data Env' = Env' {globDepth :: Int, curDepth :: Int, frees :: Set.Set Int} deriving Show


lambdaLift :: Term -> Int -> State Env Term
lambdaLift t depth = do
    Env {defs, freeVars, uniqueSupplier} <- get
    -- here lambda only can be the right part of let binding
    case t of
        -- lambdaLiftHelper is for bodyLam
        (Let nameLet (Lambda nameLam bodyLam) bodyLem) -> do
            let env = Env' {globDepth = depth + 1, curDepth = 0, frees = Set.empty }
                result@(body',s) = runState (lambdaLiftHelper bodyLam) env
                -- pick new names
            vars <- mapM (\f -> do

                Env {defs, freeVars, uniqueSupplier} <- get
                let (name', uniqueSupplier') = getNewName "arg" freeVars uniqueSupplier
                put Env {defs=defs, freeVars=Set.insert name' freeVars, uniqueSupplier=uniqueSupplier'}
                return name' ) (Set.toList (frees s))

            Env {defs, freeVars, uniqueSupplier} <- get

            let  newDef = (vars, body')

            put Env {defs=Map.insert "nameLam" newDef defs , freeVars=freeVars, uniqueSupplier=uniqueSupplier}

            let bindings = [1 .. (foldr max 0 (frees s))]
                t' = foldr (\i acc -> Apply acc (Bound i)) (Fun nameLam) bindings
            return (subst t' bodyLem)

        (Let nameLet bodyLet inLet) -> do
            t1 <- lambdaLift bodyLet depth
            t2 <- lambdaLift inLet (depth + 1)
            return (Let nameLet bodyLet inLet)
        (Con name args) -> do
            args' <- mapM (`lambdaLift` depth) args
            return (Con name args')

        -- lambda should not appear after varlift
        Lambda name t -> error "Unexpected lambda"


        _ -> return undefined

    return undefined

lambdaLiftHelper :: Term -> State Env' Term
lambdaLiftHelper t = do
    Env' {globDepth, curDepth, frees} <- get
    case t of
        (Bound i) -> if (i - curDepth) > 0 then do
                        put (Env' {globDepth=globDepth, curDepth=curDepth,frees = Set.insert (i - curDepth) frees})
                        return (Bound (i - curDepth))
                        else return (Bound i)
        (Let name t1 t2) -> do
            t1' <- lambdaLiftHelper t1
            put (Env' {globDepth=globDepth, curDepth=curDepth + 1,frees=frees})
            t2' <- lambdaLiftHelper t2
            return (Let name t1' t2')
        (Case t' branches) -> do
            t'' <- lambdaLiftHelper t'
            branches' <- mapM (\x@(name,args,t'') -> do
                    put (Env' {globDepth=globDepth, curDepth = curDepth + length args, frees=frees})
                    lambdaLiftHelper t'') branches
            return $ Case t'' (zipWith (\x@(name, args, _) y -> (name,args,y)) branches branches')
        -- at this moment t1 and t2 could only be variables, i.e. (Bound i)
        (Apply t1 t2) -> do
            t1' <- lambdaLiftHelper t1
            t2' <- lambdaLiftHelper t2
            return (Apply t1' t2')
        -- args are also simple variables, which are normaly even should not be modified
        (Con name args) -> do
            args' <- mapM lambdaLiftHelper args
            return (Con name args)
        (Lambda name body) -> do
            put (Env' {globDepth=globDepth, curDepth = curDepth + 1, frees=frees})
            body' <- lambdaLiftHelper body
            return (Lambda name body)
        -- Fold, Unfold, Free, Fun
        x -> return x

-- runSupplyVars x = runSupply x vars
--     where vars = [replicate k ['a'..'z'] | k <- [1..]] >>= sequence
