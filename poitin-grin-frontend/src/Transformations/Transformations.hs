{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

module Transformations.Transformations(module Control.Monad.State,
                                       module Term,
                                       transformP) where

import Term
import Data.List.Utils

import qualified Data.Set as Set
import qualified Data.Map as Map

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Debug.Trace

import qualified Grin.Grin as G
import qualified Data.Text as T


-- Here we will gather the list of assumptions
-- 1. Since the language is untyped, we assume that the only constructors defined are those which are used throughout the code



runPass :: (Term -> State Env Term) -> State Env ()
runPass pass = do
    Env {defs, freeVars, uniqueSupplier} <- get
    t' <- mapM_
        (\x@(name, (args, body)) -> do
            t <- pass body

            Env {defs, freeVars, uniqueSupplier} <- get

            --uniquify args each time
            put (Env {defs=addToAL defs name (args, t), freeVars=freeVars,uniqueSupplier=uniqueSupplier})

            return ()) defs
    return ()

transformP :: Prog -> (Prog, G.Program, [Tdef])
transformP p@(main', defs') = let
                                  supplier = [replicate k ['a'..'z'] | k <- [1..]] >>= sequence
                                  freeVars' = reserved' `Set.union` Set.fromList ("main" : map (\x@(name,(args,body)) -> name) defs')
                                  defs'' = (("main", ([], main')) : defs')
                                  env = Env {defs = defs'', freeVars = freeVars', uniqueSupplier = supplier }

                                  (_, defs''') = runState (runPass uniquifyNames >> runPass variableLift >> runPass (`lambdaLift` 0) >> runPass variableLift ) env
                                  (defsG, tdefs) = grinify defs'''


                                  Just (_, main) = lookup "main" (defs defs''')
                                --   (main'', defs1'') = runState (lambdaLift main 0) defs'''
                                --   rest = delFromAL (defs defs1'') "main" in
                                  rest = delFromAL (defs defs''') "main" in


                                      ((main,rest), defsG, tdefs)


reserved' :: Set.Set String
reserved' = Set.fromList ["ap"
                         ,"f"
                         ,"a"
                         ,"t"
                         ,"eval"
                         ,"apply"
                         ,"q"
                         ,"v"
                         ,"grinMain"
                         ,"m"
                         ,"result"
                         ,"w"
                         ,"GrinNode"
                         ,"GrinNodePtr"
                         ,"Go"
                         ,"go"]

-- need to know ord of every fun (this is in defs)
data GrinEnv = GrinEnv {
              defsG ::  [(String, ([String],Term))],
              freeVarsG :: Set.Set String,
              uniqueSupplierG :: [String],
              bindingsG :: Map.Map Int String,
              evalG :: Map.Map G.Tag ([G.Name], G.Exp),
              applyG :: Map.Map G.Tag ([G.Name], G.Exp)}

apG :: G.Def
apG = G.Def (G.NM {G.unNM="ap"}) [G.NM {G.unNM="f"},G.NM {G.unNM="a"}]
                            (G.EBind (G.SApp (G.NM {G.unNM="eval"}) [G.Var G.NM {G.unNM="f"}])
                                     (G.Var G.NM {G.unNM="t"})
                                     (G.SApp (G.NM {G.unNM="apply"}) [G.Var G.NM {G.unNM="t"},
                                                                      G.Var G.NM {G.unNM="a"}])
                            )


-- every function should return a value (Node in current implementations, since we have no primitives)

grinify :: Env -> (G.Program, [Tdef])
grinify env@(Env defs freeVars uniqueSupplier) =
        let envG = GrinEnv defs freeVars uniqueSupplier Map.empty Map.empty Map.empty
            calc = mapM (\def@(name, (args, t)) -> do
                    -- pick new names for args
                    GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get

                    let helper' = \(f,u,a) arg -> let (name', u') = getNewName arg f u in
                                                    (Set.insert name' f, u', name' : a)
                        (free', uniqueSupplier', args') = foldl helper' (freeVarsG, uniqueSupplierG, []) (reverse args)
                        newBindings = foldl (\m x@(i,v) -> Map.insert i v m) Map.empty (zip (reverse [0 .. (length args' - 1)]) args')

                    put (GrinEnv {defsG=defsG, freeVarsG=free',uniqueSupplierG=uniqueSupplier', bindingsG=newBindings, evalG=evalG, applyG=applyG})

                    exprG <- grinifyHelper t Strict

                    -- let name' = if name == "main" then "grinMain" else name
                    let name' = name

                    return (G.Def (G.NM {G.unNM=T.pack name'}) (map (\x -> G.NM {G.unNM=T.pack x}) args') exprG)

                 ) defs

            (result, s) = runState calc envG
            defsG' = apG : result
            (evalGAlts, s') = runState (mapM grinifyEval defsG') s
            (applyGAlts, s'') = runState (mapM grinifyApply defsG') s'

            apGAlt = G.Alt
            evalGAlts' =  concat evalGAlts ++ map (\(tag, body@(args, exp)) -> G.Alt (G.NodePat tag args) exp) (Map.toList $ evalG s'')
            applyGAlts' = concat applyGAlts ++ map (\(tag, body@(args, exp)) -> G.Alt (G.NodePat tag args) exp) (Map.toList $ applyG s'')

            -- this is needed for grin to dataflow generation. This tdefs will contain single GrinNode type with all the pointers.
            -- Constructors without arguments are supplied with extra "Go" argument for consistency
            tdefs = [
                Data "GrinNodePtr" [] [Constr "GrinNodePtr" [Tcon "GrinNode"]]
                , Data "GrinNode" []  (map (\x@(G.Alt cpat@(G.NodePat t args) _) ->
                        Constr (filter (/= ' ') ((show . G.tagType) t ++ (G.nameString . G.tagName) t)) (case args of [] -> [Tcon "Go"]
                                                                                                                      xs -> map (const $ Tcon "GrinNodePtr") args)) evalGAlts')
                ]

            evalG' = G.Def (G.NM {G.unNM="eval"}) [G.NM {G.unNM="q"}]
                        (G.EBind (G.SFetchI (G.NM {G.unNM="q"}) Nothing)
                                 (G.Var G.NM{G.unNM="v"})
                                 (G.EBind
                                    (G.ECase (G.Var G.NM {G.unNM="v"}) evalGAlts')

                                    (G.Var G.NM {G.unNM="w"})

                                    -- (G.EBind  (G.SUpdate (G.NM {G.unNM="q"}) (G.Var (G.NM {G.unNM="w"})))
                                    --         G.Unit
                                    --         (G.SReturn (G.Var G.NM {G.unNM="w"})))
                                    (G.SReturn (G.Var G.NM {G.unNM="w"})) -- SUpdate is needed for laziness, so I omit it for now

                                 )
                        )
            applyG' = G.Def (G.NM {G.unNM="apply"}) [G.NM {G.unNM="f'"}, G.NM {G.unNM="a''"}] (G.ECase (G.Var G.NM {G.unNM="f'"}) applyGAlts')

            grinMainBody = G.EBind (G.SApp (G.NM {G.unNM="main"}) []) (G.Var (G.NM {G.unNM="m"}))
                                --    (G.EBind (G.SApp (G.NM {G.unNM="eval"}) [G.Var (G.NM {G.unNM="m"})]) (G.Var (G.NM {G.unNM="result"}))
                                    -- (G.SReturn (G.Var (G.NM {G.unNM="result"}))))
                                    (G.SReturn (G.Var (G.NM {G.unNM = "m"})))
            grinMainDef = G.Def (G.NM {G.unNM="grinMain"}) [] grinMainBody in
            -- add apply, ap, eval
            -- ap is straightforward, eval is for each fun and for each encountered c-tor, apply is only for funs and c-tors
            (G.Program [] (grinMainDef : result ++ [applyG', evalG', apG]), tdefs)


grinifyApply :: G.Exp -> State GrinEnv [G.Alt]
grinifyApply x@(G.Def name args body) =
        mapM (\i -> do
    GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get
    let (name',uniqueSupplierG') = getNewName "patP_app" freeVarsG uniqueSupplierG

        (args'', freeVarsG'', uniqueSupplierG'') = foldl (\(acc,f,u) _ -> let (name',uniqueSupplierG') = getNewName "pat" f u in
                                    (name' : acc, Set.insert name' f, uniqueSupplierG')) ([], Set.insert name' freeVarsG, uniqueSupplierG') [1 .. (length args - i)]

    put (GrinEnv {defsG=defsG, freeVarsG=freeVarsG'', uniqueSupplierG=uniqueSupplierG'', bindingsG=bindingsG, evalG=evalG,applyG=applyG})
    let body = if i == 1 then G.SApp name (map (\x -> G.Var (G.NM {G.unNM=T.pack x})) args'' ++ [G.Var (G.NM {G.unNM="a''"})])
                           else G.SReturn (G.ConstTagNode (G.Tag (G.P (i-1)) name) (map (\x -> G.Var (G.NM {G.unNM=T.pack x})) args'' ++ [G.Var (G.NM {G.unNM="a''"})]) )
    return (G.Alt (G.NodePat (G.Tag (G.P i) name) (map (\x -> G.NM {G.unNM=T.pack x}) args'' )) body)) (reverse [1 .. (length args)])


grinifyApply _ = error "expected G.Def in apply"

grinifyEval :: G.Exp -> State GrinEnv [G.Alt]
grinifyEval x@(G.Def name args body) = do
    GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get
    let (args', freeVarsG', uniqueSupplierG') = foldl (\(acc,f,u) _ -> let (name',uniqueSupplierG') = getNewName "pat" f u in
                                            (name' : acc, Set.insert name' f, uniqueSupplierG')) ([], freeVarsG, uniqueSupplierG) args
        -- (resultName, uniqueSupplierG'') = getNewName "z" freeVarsG' uniqueSupplierG'
        -- freeVarsG'' = Set.insert resultName freeVarsG'
        alt = G.Alt (G.NodePat (G.Tag G.F name)
                        (map (\a -> G.NM {G.unNM=T.pack  a}) args'))
                        (G.SApp name (map (\a -> G.Var $ G.NM {G.unNM=T.pack  a}) args'))

                        -- (G.EBind (G.SApp name (map (\a -> G.Var $ G.NM {G.unNM=T.pack  a}) args'))
                        --          (G.Var G.NM {G.unNM=T.pack resultName})
                        --          (G.EBind (G.SUpdate (G.NM {G.unNM="q"}) (G.Var (G.NM {G.unNM = T.pack resultName}))) G.Unit (G.SReturn (G.Var (G.NM {G.unNM=T.pack resultName})))))
    -- generate all partiall applied evals
    put (GrinEnv {defsG=defsG, freeVarsG=freeVarsG', uniqueSupplierG=uniqueSupplierG',bindingsG=bindingsG, evalG=evalG, applyG=applyG})
    alts <- mapM (\i -> do
            GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get
            let (name',uniqueSupplierG') = getNewName "patP" freeVarsG uniqueSupplierG

                (args'', freeVarsG'', uniqueSupplierG'') = foldl (\(acc,f,u) _ -> let (name',uniqueSupplierG') = getNewName "pat" f u in
                                            (name' : acc, Set.insert name' f, uniqueSupplierG')) ([], Set.insert name' freeVarsG, uniqueSupplierG') [1 .. (length args - i)]

            put (GrinEnv {defsG=defsG, freeVarsG=freeVarsG'', uniqueSupplierG=uniqueSupplierG'', bindingsG=bindingsG, evalG=evalG,applyG=applyG})
            return (G.Alt (G.NodePat (G.Tag (G.P i) name) (map (\x -> G.NM {G.unNM=T.pack x}) args'' )) (G.SReturn (G.Var (G.NM {G.unNM="v"}))))
        ) (reverse [1 .. (length args)])

    return (alt : alts)

grinifyEval _ = error "expected only G.Def"

-- Strict returs a value while non-strict returns a pointer
data TransRule = Strict | NonStrict

grinifyHelper :: Term -> TransRule -> State GrinEnv G.Exp
grinifyHelper t rule = do

    GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get

    case t of
        Let name t1 t2 -> do
            -- variable is always non-strict ?
            t1' <- G.SBlock <$> grinifyHelper t1 NonStrict
            let newBindings = Map.insert 0 name (Map.mapKeys (+1) bindingsG)

            GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get

            -- let (name1', uniqueSupplierG1') = getNewName "bind" freeVarsG uniqueSupplierG
                -- (name2', uniqueSupplierG2') = getNewName "bind" (Set.insert name1' freeVarsG) uniqueSupplierG1'

                -- store = G.EBind (G.SApp (G.NM {G.unNM="eval"}) [G.Var (G.NM{G.unNM = T.pack name1'})]) (G.Var (G.NM {G.unNM=T.pack name2'})) (G.SStore (G.Var (G.NM {G.unNM=T.pack name2'})))
                -- innerLet = G.EBind t1' (G.Var (G.NM{G.unNM = T.pack name1'})) store
            put (GrinEnv {defsG=defsG, bindingsG=newBindings, freeVarsG=freeVarsG,uniqueSupplierG=uniqueSupplierG,evalG=evalG,applyG=applyG})

            -- G.EBind (G.SBlock innerLet) (G.Var (G.NM {G.unNM=T.pack name})) <$> grinifyHelper t2 NonStrict
            case rule of
                Strict -> G.EBind t1' (G.Var (G.NM {G.unNM=T.pack name})) <$> grinifyHelper t2 Strict
                NonStrict -> G.EBind t1' (G.Var (G.NM {G.unNM=T.pack name})) <$> grinifyHelper t2 NonStrict
        -- applies only var to var
        Apply (Bound i1) (Bound i2) -> do

            let (Just name1) = Map.lookup i1 bindingsG
                (Just name2) = Map.lookup i2 bindingsG

            case rule of
                NonStrict -> return (G.SStore
                    (G.ConstTagNode
                        (G.Tag {G.tagType=G.F, G.tagName=G.NM {G.unNM="ap"}})
                        [
                            G.Var (G.NM {G.unNM=T.pack name1}),
                            G.Var (G.NM {G.unNM=T.pack name2})
                        ]
                    ))
                Strict -> return (G.SApp
                    (G.NM {G.unNM="ap"})
                        [
                            G.Var (G.NM {G.unNM=T.pack name1}),
                            G.Var (G.NM {G.unNM=T.pack name2})
                        ]
                    )
                -- Strict -> return (G.SReturn
                --     (G.ConstTagNode
                --         (G.Tag {G.tagType=G.F, G.tagName=G.NM {G.unNM="ap"}})
                --         [
                --             G.Var (G.NM {G.unNM=T.pack name1}),
                --             G.Var (G.NM {G.unNM=T.pack name2})
                --         ]
                --     ))

        -- It is needed that lists, for example, only contained evaluated terms, i.e. values. 
        -- Thus, before doing an insert into list the item should be eval'ed
        -- But eval returns node values instead of pointers to evaluated values and hence the whole list will end up in registers instead of heap 

        -- Everything is a pointer except for main's result it is a value
        -- args are variables
        Con name args -> do
            let (Just args') = mapM (\x@(Bound i) -> Map.lookup i bindingsG) args
                conTag = (G.Tag {G.tagType=G.C, G.tagName=G.NM {G.unNM=T.pack name}})

                helper' = \(f,u,a) arg -> let (name', u') = getNewName arg f u in
                                                    (Set.insert name' f, u', name' : a)
                (freeApply', uniqueSupplierApply', argsApply') = foldl helper' (freeVarsG, uniqueSupplierG, []) args'
                (freeEval', uniqueSupplierEval', argsEval') = foldl helper' (freeApply', uniqueSupplierApply', []) argsApply'

                -- altBodyApply = G.SReturn (G.ConstTagNode conTag  (map (\x -> G.Var (G.NM {G.unNM = T.pack x})) argsApply'))
                altBodyApply = G.SReturn (G.Var (G.NM {G.unNM="f'"}))
                entryApply = (map (\x -> G.NM {G.unNM=T.pack x}) argsApply', altBodyApply)

                -- altBodyEval = G.SReturn (G.ConstTagNode conTag  (map (\x -> G.Var (G.NM {G.unNM = T.pack x})) argsEval'))
                altBodyEval = G.SReturn (G.Var (G.NM {G.unNM="v"}))
                entryEval = (map (\x -> G.NM {G.unNM=T.pack x}) argsEval', altBodyEval)

            put (GrinEnv {defsG=defsG, bindingsG=bindingsG, freeVarsG=freeEval',uniqueSupplierG=uniqueSupplierEval',evalG=  Map.insert conTag entryEval evalG,applyG=Map.insert conTag entryApply applyG})

            case rule of
                Strict -> return (G.SReturn (G.ConstTagNode
                                conTag
                                (map (\x -> G.Var (G.NM {G.unNM = T.pack x})) args')
                            ))
                NonStrict -> return (G.SStore (G.ConstTagNode
                                conTag
                                (map (\x -> G.Var (G.NM {G.unNM = T.pack x})) args')
                            ))
        Case (Bound i) branches -> do
            let (name, uniqueSupplierG') = getNewName "z" freeVarsG uniqueSupplierG
                (Just iname) = Map.lookup i bindingsG
                evalI = G.SApp (G.NM {G.unNM=T.pack "eval"}) [G.Var (G.NM (T.pack iname))]
            put (GrinEnv {defsG=defsG, bindingsG=bindingsG,freeVarsG=Set.insert name freeVarsG, uniqueSupplierG=uniqueSupplierG',evalG=evalG, applyG=applyG})

            GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get

            let oldBindings = bindingsG

            alts <- mapM (\b@(cname, cargs, body) -> do
                let newBindings = foldl (\acc (i,arg) -> Map.insert i arg acc) (Map.mapKeys (+ length cargs) bindingsG) (zip (reverse [0 .. length cargs - 1]) cargs)

                GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get
                put (GrinEnv {defsG=defsG, bindingsG=newBindings, freeVarsG=freeVarsG, uniqueSupplierG=uniqueSupplierG, evalG=evalG, applyG=applyG})

                body' <- grinifyHelper body Strict

                let alt = G.Alt (G.NodePat (G.Tag G.C (G.NM {G.unNM=T.pack cname})) (map (\x -> G.NM {G.unNM=T.pack x}) cargs))
                return $ alt body') branches

            GrinEnv {defsG, freeVarsG, uniqueSupplierG, bindingsG, evalG, applyG} <- get
            put (GrinEnv {defsG=defsG, bindingsG=oldBindings, freeVarsG=freeVarsG, uniqueSupplierG=uniqueSupplierG, evalG=evalG, applyG=applyG})

            let e = G.EBind evalI (G.Var (G.NM {G.unNM=T.pack name})) (G.ECase (G.Var (G.NM {G.unNM=T.pack name})) alts)

            return e

        -- pay attention to the case when fun has no arguments but then it cannot be inside apply
        Fun name -> do
            let (Just (args, _)) = lookup name defsG
            if null args then
               case rule of
                    NonStrict -> return (G.SStore (G.ConstTagNode (G.Tag G.F (G.NM {G.unNM =T.pack name})) []))
                    Strict -> return (G.SReturn (G.ConstTagNode (G.Tag G.F (G.NM {G.unNM =T.pack name})) []))
            else
                case rule of
                    NonStrict -> return (G.SStore (G.ConstTagNode (G.Tag (G.P (length args)) (G.NM {G.unNM =T.pack name})) []))
                    Strict -> return (G.SReturn (G.ConstTagNode (G.Tag (G.P (length args)) (G.NM {G.unNM =T.pack name})) []))
        (Bound i) -> do
            let (Just nameI) = Map.lookup i bindingsG
            case rule of
                NonStrict -> return (G.SReturn (G.Var (G.NM {G.unNM=T.pack nameI})))
                Strict -> do
                    let  (name, uniqueSupplierG') = getNewName "ret" freeVarsG uniqueSupplierG
                         body = G.EBind (G.SApp (G.NM {G.unNM = "eval"}) [G.Var (G.NM {G.unNM = T.pack nameI})]) (G.Var (G.NM {G.unNM = T.pack name})) (G.SReturn (G.Var (G.NM {G.unNM = T.pack name})))

                    put (GrinEnv {defsG=defsG, bindingsG=bindingsG, freeVarsG=Set.insert name freeVarsG, uniqueSupplierG=uniqueSupplierG',evalG=evalG,applyG=applyG})
                    return body

                -- (name, uniqueSupplierG') = getNewName "var" freeVarsG uniqueSupplierG
                -- body = G.EBind (G.SApp (G.NM {G.unNM="eval"}) [G.Var (G.NM {G.unNM=T.pack nameI})]) (G.Var (G.NM {G.unNM=T.pack name})) (G.SReturn (G.Var (G.NM {G.unNM=T.pack name})))

            -- return body
        -- no unfold, fold, free, and lambda
        x -> error $ "Unexpected pattern: unfold, fold, free or lambda " ++ show x



data Env = Env {defs ::  [(String, ([String],Term))],
                freeVars :: Set.Set String,
                uniqueSupplier :: [String]
                }

-- here we just rename all let bindings so they introduce only new variable names (though they are not used explicitly due to de-brujin indexes)


uniquifyNames :: Term -> State Env Term
uniquifyNames t = do
    Env {defs, freeVars, uniqueSupplier} <- get

    case t of
        Lambda s t' -> do
            t'' <- uniquifyNames t'
            return (Lambda s t'')
        Con s args@(x:xs) ->
            Con s <$> mapM uniquifyNames args
        Apply t1 t2 -> do
            t1' <- uniquifyNames t1
            t2' <- uniquifyNames t2
            return (Apply t1' t2')
        Case t' l@(x:xs) -> do
            scrut <- uniquifyNames t'
            branches <- mapM (\x@(name,args,t'') -> do
                t''' <- uniquifyNames t''
                args' <- mapM (\y -> do
                    Env {defs, freeVars, uniqueSupplier} <- get
                    let (name', uniqueSupplier') = getNewName y freeVars uniqueSupplier
                    put (Env {defs=defs, freeVars=Set.insert name' freeVars, uniqueSupplier=uniqueSupplier'})
                    return name'
                    ) args
                return (name, args', t''')
                ) l

            return $ Case scrut branches
        Let name t1 t2 -> do

            -- if name `Set.member` freeVars then do
            --     let (prefix, end) = span (\x -> (name ++ "_" ++ x) `Set.member` freeVars) uniqueSupplier
            --         (x:xs) = end in do
            --                 put (Env {defs = defs, freeVars = Set.insert (name ++ "_" ++ x) freeVars, uniqueSupplier=xs})
            --                 t1' <- uniquifyNames t1
            --                 t2' <- uniquifyNames t2
            --                 return $ Let (name ++ "_" ++ x) t1' t2'
            -- else do
            --     put (Env {defs = defs, freeVars = Set.insert name freeVars, uniqueSupplier=uniqueSupplier})
            --     t1' <- uniquifyNames t1
            --     t2' <- uniquifyNames t2
            --     return (Let name t1' t2')
            let (name', uniqueSupplier') = getNewName name freeVars uniqueSupplier

            put (Env {defs = defs, freeVars = Set.insert name' freeVars, uniqueSupplier = uniqueSupplier'})
            t1' <- uniquifyNames t1
            t2' <- uniquifyNames t2
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
                --    let (name1, uniqueSupplier1) = getNewName "var" freeVars uniqueSupplier
                --    put (Env {defs = defs, freeVars = Set.insert name1 freeVars, uniqueSupplier = uniqueSupplier1})

                   body' <- variableLift body

                   return (Lambda name body')
               -- each con's parameter should be a variable
                Con c ts -> do
                   ts' <- mapM variableLift ts
                   let binds = reverse [Bound i | i <- [0 .. length ts' - 1]]
                   names' <- sequence [(\(t', i) -> do
                           Env {defs, freeVars, uniqueSupplier} <- get

                           let (name', uniqueSupplier') = getNewName "c_bind" freeVars uniqueSupplier

                           put (Env {defs = defs, freeVars = Set.insert name' freeVars, uniqueSupplier = uniqueSupplier'})
                        -- t' from ts', i.e. let v_1 = t1 in let v_2 = t2 in C v_1 v_2
                           return (Let name' (shift i t'))) t' | t' <- zip ts' [0 .. length ts' - 1]]

                   return $ foldr ($) (Con c binds) names'
                -- case does not introduce new bindings  
                Case t' branches -> do
                    let (name', uniqueSupplier') = getNewName "scrut" freeVars uniqueSupplier
                    put (Env {defs = defs, freeVars = Set.insert name' freeVars, uniqueSupplier = uniqueSupplier'})


                    t1' <- variableLift t'

                    -- shift' is really important here

                    branches' <- mapM (\x@(name,args,t'') -> variableLift (shift' (length args) 1  t'')) branches

                    return $ Let name' t1' (Case (Bound 0) (zipWith (\x@(name, args, _) y -> (name,args, y)) branches branches'))

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
                Fold {} -> error "unexpected Fold"

                x -> return x

data Env' = Env' {globDepth :: Int, curDepth :: Int, frees :: Set.Set Int} deriving Show


lambdaLift :: Term -> Int -> State Env Term
lambdaLift t depth = do
    Env {defs, freeVars, uniqueSupplier} <- get
    -- here lambda only can be the right part of let binding
    case t of
        -- lambdaLiftHelper is for bodyLam
        -- (Let nameLet (Lambda nameLam bodyLam) bodyLet) -> do
        --     let env = Env' {globDepth = depth + 1, curDepth = 0, frees = Set.empty }
        --         result@(body',s) = runState (lambdaLiftHelper bodyLam) env
        --         -- pick new names
        --         bindings = [1 .. (foldr max 0 (frees s))]
        --     vars <- mapM (\f -> do

        --         Env {defs, freeVars, uniqueSupplier} <- get
        --         let (name', uniqueSupplier') = getNewName "arg" freeVars uniqueSupplier
        --         put Env {defs=defs, freeVars=Set.insert name' freeVars, uniqueSupplier=uniqueSupplier'}
        --         return name' ) (0 : bindings)

        --     Env {defs, freeVars, uniqueSupplier} <- get

        --     let  newDef = (vars, body')
        --          (name', uniqueSupplier') = getNewName "fun" freeVars uniqueSupplier  

        --     put Env {defs=addToAL defs name' newDef, freeVars=Set.insert name' freeVars, uniqueSupplier=uniqueSupplier}

        --     let t' = foldr (\i acc -> Apply acc (Bound i)) (Fun name') (trace ("BINDINGS: " ++ show bindings) (bindings))
        --     return (Let nameLet (trace ("t' : " ++ show t') (shift (-1) t')) bodyLet)
        (Lambda name body) -> do
            body' <- lambdaLift body 0
            let env = Env' {globDepth = depth + 1, curDepth = 0, frees = Set.empty}
                result@(body'',s) = runState (lambdaLiftHelper body') env
                -- pick new names
                bindings = [1 .. (foldr max 0 (frees s))]
            vars <- mapM (\f -> do

                Env {defs, freeVars, uniqueSupplier} <- get
                let (name', uniqueSupplier') = getNewName "arg" freeVars uniqueSupplier
                put Env {defs=defs, freeVars=Set.insert name' freeVars, uniqueSupplier=uniqueSupplier'}
                return name' ) (0 : bindings)

            Env {defs, freeVars, uniqueSupplier} <- get
            let  newDef = (vars, body'')
                 (name', uniqueSupplier') = getNewName "fun" freeVars uniqueSupplier

            put Env {defs=addToAL defs name' newDef, freeVars=Set.insert name' freeVars, uniqueSupplier=uniqueSupplier'}

            let t' = foldr (\i acc -> Apply acc (Bound i)) (Fun name') bindings
            return ( shift (-1) t')


        (Let nameLet bodyLet inLet) -> do
            t1 <- lambdaLift bodyLet depth
            t2 <- lambdaLift inLet (depth + 1)
            return (Let nameLet t1 t2)
        (Con name args) -> do
            args' <- mapM (`lambdaLift` depth) args
            return (Con name args')
        (Apply t1 t2) -> do
            t1' <- lambdaLift t1 depth
            t2' <- lambdaLift t2 depth
            return (Apply t1' t2')
        (Case scrut alts) -> do
            alts' <- mapM (\x@(con, args, t) -> lambdaLift t depth) alts
            return (Case scrut (zipWith (\t r@(con, args, _) -> (con, args, t)) alts' alts))
        x -> return x 
            

lambdaLiftHelper :: Term -> State Env' Term
lambdaLiftHelper t = do
    Env' {globDepth, curDepth, frees} <- get
    case t of
        (Bound i) -> if i - curDepth > 0 then do
                        put (Env' {globDepth=globDepth, curDepth=curDepth,frees = Set.insert (i - curDepth) frees})
                        return (Bound i)
                        else return (Bound i)
        (Let name t1 t2) -> do
            t1' <- lambdaLiftHelper t1

            let (globDepth', curDepth') = (globDepth, curDepth)
            Env' {globDepth, curDepth, frees} <- get
            put (Env' {globDepth=globDepth', curDepth=curDepth' + 1,frees=frees})

            t2' <- lambdaLiftHelper t2
            return (Let name t1' t2')
        (Case t' branches) -> do
            t'' <- lambdaLiftHelper t'

            let (globDepth', curDepth') = (globDepth, curDepth)
            Env' {globDepth, curDepth, frees} <- get

            branches' <- mapM (\x@(name,args,t'') -> do
                    put (Env' {globDepth=globDepth', curDepth = curDepth' + length args, frees=frees})
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
            return (Con name args')
        -- lambda is only in let
        (Lambda name body) -> do
            put (Env' {globDepth=globDepth, curDepth = curDepth + 1, frees=frees})
            body' <- lambdaLiftHelper body
            return (Lambda name body')
        -- Fold, Unfold, Free, Fun
        x -> return x

-- runSupplyVars x = runSupply x vars
--     where vars = [replicate k ['a'..'z'] | k <- [1..]] >>= sequence
