{-# LANGUAGE FlexibleInstances, OverloadedStrings, BangPatterns #-}

module Language.Nano.TypeCheck where

import Language.Nano.Types
import Language.Nano.Parser

import qualified Data.List as L
import           Text.Printf (printf)  
import           Control.Exception (throw)

--------------------------------------------------------------------------------
typeOfFile :: FilePath -> IO Type
typeOfFile f = parseFile f >>= typeOfExpr

typeOfString :: String -> IO Type
typeOfString s = typeOfExpr (parseString s)

typeOfExpr :: Expr -> IO Type
typeOfExpr e = do
  let (!st, t) = infer initInferState preludeTypes e
  if (length (stSub st)) < 0 then throw (Error ("count Negative: " ++ show (stCnt st)))
  else return t

--------------------------------------------------------------------------------
-- Problem 1: Warm-up
--------------------------------------------------------------------------------

-- | Things that have free type variables
class HasTVars a where
  freeTVars :: a -> [TVar]

-- | Type variables of a type
instance HasTVars Type where
  freeTVars TInt = []
  freeTVars TBool = []
  freeTVars (TVar x) = [x]
  freeTVars (TList x) = freeTVars x
  freeTVars (a :=> b) = L.nub (freeTVars a ++ freeTVars b)

-- | Free type variables of a poly-type (remove forall-bound vars)
instance HasTVars Poly where
  freeTVars (Mono a) = freeTVars a
  freeTVars (Forall a b) = L.delete a (L.nub (freeTVars b))

-- | Free type variables of a type environment
instance HasTVars TypeEnv where
  freeTVars gamma   = concat [freeTVars s | (x, s) <- gamma]  
  
-- | Lookup a variable in the type environment  
lookupVarType :: Id -> TypeEnv -> Poly
lookupVarType x ((y, s) : gamma)
  | x == y    = s
  | otherwise = lookupVarType x gamma
lookupVarType x [] = throw (Error ("unbound variable: " ++ x))

-- | Extend the type environment with a new biding
extendTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extendTypeEnv x s gamma = (x,s) : gamma  

-- | Lookup a type variable in a substitution;
--   if not present, return the variable unchanged
lookupTVar :: TVar -> Subst -> Type
lookupTVar a sub | null sub = TVar a
  | a == fst (head sub) = snd (head sub)
  | otherwise = lookupTVar a (tail sub)

-- | Remove a type variable from a substitution
removeTVar :: TVar -> Subst -> Subst
removeTVar a sub = sub L.\\ [(a, lookupTVar a sub)]
     
-- | Things to which type substitutions can be apply
class Substitutable a where
  apply :: Subst -> a -> a
  
-- | Apply substitution to type
instance Substitutable Type where  
  apply sub t         = case t of
    TInt -> TInt
    TBool -> TBool
    TVar x -> lookupTVar x sub
    a :=> b -> apply sub a :=> apply sub b
    TList x -> list (apply sub x)

-- | Apply substitution to poly-type
instance Substitutable Poly where    
  apply sub s         = case s of
    Mono x -> Mono (apply sub x)
    Forall a b -> Forall a (apply (removeTVar a sub) b)

-- | Apply substitution to (all poly-types in) another substitution
instance Substitutable Subst where  
  apply sub to = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip to
      
-- | Apply substitution to a type environment
instance Substitutable TypeEnv where  
  apply sub gamma = zip keys $ map (apply sub) vals
    where
      (keys, vals) = unzip gamma
      
-- | Extend substitution with a new type assignment
extendSubst :: Subst -> TVar -> Type -> Subst
extendSubst s a t = foldr f [(a, apply sub t)] s
  where
    f x y = y++[(fst x, apply sub (snd x))]
    sub = (a, t):s
      
--------------------------------------------------------------------------------
-- Problem 2: Unification
--------------------------------------------------------------------------------
      
-- | State of the type inference algorithm      
data InferState = InferState { 
    stSub :: Subst -- ^ current substitution
  , stCnt :: Int   -- ^ number of fresh type variables generated so far
} deriving (Eq,Show)

-- | Initial state: empty substitution; 0 type variables
initInferState = InferState [] 0

-- | Fresh type variable number n
freshTV n = TVar $ "a" ++ show n      
    
-- | Extend the current substitution of a state with a new type assignment   
extendState :: InferState -> TVar -> Type -> InferState
extendState (InferState sub n) a t = InferState (extendSubst sub a t) n
        
-- | Unify a type variable with a type; 
--   if successful return an updated state, otherwise throw an error
unifyTVar :: InferState -> TVar -> Type -> InferState
unifyTVar st a t = case t of
  TInt -> extendState st a t
  TBool -> extendState st a t
  TVar x -> if a == x then st else extendState st a t
  _ -> if apply (stSub tst) (TVar a) == apply (stSub tst) t then tst else throw (Error ("type error: cannot unify " ++ a ++ " and " ++ show t ++ " (occurs check)"))
  where
    tst = extendState st a t
    
-- | Unify two types;
--   if successful return an updated state, otherwise throw an error
unify :: InferState -> Type -> Type -> InferState
unify st TInt TInt = st
unify st TBool TBool = st
unify st (TVar x) a = unifyTVar (InferState (removeTVar x (stSub st)) (stCnt st)) x a
unify st a (TVar x) = unifyTVar (InferState (removeTVar x (stSub st)) (stCnt st)) x a
unify st (a :=> b) (c :=> d) = unify ust (apply sub b) (apply sub d)
  where
    ust = unify st a c
    sub = stSub ust
unify st (TList a) (TList b) = unify st a b
unify _ a b = throw (Error ("type error: cannot unify " ++ show a ++ " and " ++ show b))

--------------------------------------------------------------------------------
-- Problem 3: Type Inference
--------------------------------------------------------------------------------    
  
infer :: InferState -> TypeEnv -> Expr -> (InferState, Type)
infer st _   (EInt _)          = (st, TInt)
infer st _   (EBool _)         = (st, TBool)
infer st gamma (EVar x)        = inf
  where
    inf = case lp of
       Just f -> (st', t)
        where
          (cnt, t) = instantiate (stCnt st) f
          st' = InferState (stSub st) cnt
       Nothing -> do
        let tv = freshTV (stCnt st)
        let sus = unify (InferState (stSub st) (stCnt st + 1)) (tv :=> tv) (lookupTVar x (stSub st)) 
        (sus, apply (stSub st) tv)
    lp = lookup x gamma
infer st gamma (ELam x body)   = (stub, tX' :=> tBody)
  where
    env = extendTypeEnv x tX gamma
    at = freshTV (stCnt st)
    tX = Mono at
    st' = InferState (stSub st) (stCnt st + 1)
    (stub, tBody) = infer st' env body
    tX' = apply (stSub stub) at 
infer st gamma (EApp e1 e2)    = (st4, t3)
  where
    ftv = freshTV (stCnt st2)
    (st1, t1) = infer st gamma e1
    (st2, t2) = infer st1 (apply (stSub st1) gamma) e2
    st3 = unify st2 (apply (stSub st2) t1) (t2 :=> ftv)
    --st3 = unify st2 t1 (t2 :=> freshTV (stCnt st2))
    st3' = InferState (stSub st3) (stCnt st3 + 1)
    t3 = apply (stSub st3) ftv
    sub [] = []
    sub (x:xs) | fst x `elem` ["b1", "b2", "b3", "b4", "b5", "b6", "b6"] = sub xs
               | otherwise = x:sub xs
    st4 = InferState (sub (stSub st3')) (stCnt st3')
infer st gamma (ELet x e1 e2)  = (sub3, t3)
  where
    (sub1, t1) = infer st gamma e1
    env' = apply (stSub sub1) gamma
    env = extendTypeEnv x (generalize env' t1) env'
    (sub2, _) = infer sub1 env e1
    (sub3, t3) = infer sub2 env e2
infer st gamma (EBin op e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp opVar e1) e2
    opVar = EVar (show op)
infer st gamma (EIf c e1 e2) = infer st gamma asApp
  where
    asApp = EApp (EApp (EApp ifVar c) e1) e2
    ifVar = EVar "if"    
infer st gamma ENil = infer st gamma (EVar "[]")

-- | Generalize type variables inside a type
generalize :: TypeEnv -> Type -> Poly
generalize gamma t = pp ftvs
  where
    same [] _ = []
    same (x:xs) ys = if x `elem` ys then same xs (L.delete x ys) else x:same xs ys
    ftvs = same (freeTVars t) (freeTVars gamma)
    pp f = case f of
      [] -> Mono t
      (x:xs) -> Forall x (pp xs)
    
-- | Instantiate a polymorphic type into a mono-type with fresh type variables
instantiate :: Int -> Poly -> (Int, Type)
instantiate n s = (nt, t)
  where
    nt = length bvs + n
    t' = m s
    m (Mono a) = a
    m (Forall _ b) = m b
    bvs = gbvs s
    gbvs (Mono _) = []
    gbvs (Forall a b) = a:gbvs b
    fsh = gfs bvs
    gfs [] = []
    gfs (x:xs) = freshTV (dex x bvs n):gfs xs
    dex x l n' = case L.elemIndex x l of
      Just a -> a + n'
      _ -> error "CUM"
    sub = zip bvs fsh
    t = apply sub t'
      
-- | Types of built-in operators and functions      
preludeTypes :: TypeEnv
preludeTypes =
  [ ("+",    Mono $ TInt :=> TInt :=> TInt)
  , ("-",    Mono $ TInt :=> TInt :=> TInt)
  , ("*",    Mono $ TInt :=> TInt :=> TInt)
  , ("/",    Mono $ TInt :=> TInt :=> TInt)
  , ("==",   Mono $ "b1" :=> "b1" :=> TBool)
  , ("!=",   Mono $ "b2" :=> "b2" :=> TBool)
  , ("<",    Mono $ TInt :=> TInt :=> TBool)
  , ("<=",   Mono $ TInt :=> TInt :=> TBool)
  , ("&&",   Mono $ TBool :=> TBool :=> TBool)
  , ("||",   Mono $ TBool :=> TBool :=> TBool)
  , ("if",   Mono $ TBool :=> "b3" :=> "b3" :=> "b3")
  -- lists: 
  , ("[]",   Mono $ TList "b4")
  , (":",    Mono $ "b5" :=> TList "b5" :=> TList "b5")
  , ("head", Mono $ TList "b6" :=> "b6")
  , ("tail", Mono $ TList "b7" :=> TList "b7")
  ]
