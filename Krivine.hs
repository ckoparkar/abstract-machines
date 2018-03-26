module Krivine where

newtype Env = Env [Clos]
  deriving (Read, Show, Eq, Ord)

-- lookup' :: Var -> [(Var,Clos)] -> Clos
-- lookup' v env = fromJust $ lookup v env

lookup' :: Int -> [Clos] -> Clos
lookup' i ls =  ls !! i

data Val = VNum Int
         | VLam Exp Env
  deriving (Read, Show, Eq, Ord)

type Var   = Int
type Clos  = (Exp,Env)
type Stack = [Clos]
type State = (Clos,Stack)

data Exp = VarE Var
         | LamE Exp
         | AppE Exp Exp
         | LitE Int
         | SuccE Exp
         | SuccK
         | PlusE Exp Exp
         | PlusK Exp
  deriving (Read, Show, Eq, Ord)

type KMR = Either Val State

k :: State -> KMR
k s = case s of
          ((LitE n, _env), [])     -> Left (VNum n)
          ((LitE n, env), nxt:stk) -> k (nxt, (LitE n,env):stk)
          ((VarE v, Env env), stk) -> k (lookup' v env, stk)
          ((AppE a b, env), stk)   -> k ((a,env), (b,env):stk)
          ((LamE rhs, env), [])    -> Left $ VLam rhs env
          ((LamE rhs, (Env env)), c:stk)  -> k ((rhs,Env (c:env)), stk)
          ((SuccE rhs, env), stk)         -> k ((rhs,env), (SuccK, env):stk)
          ((SuccK, env), (LitE n, _):stk) -> k ((LitE (n+1), env), stk)
          ((PlusE a b, env), stk)         -> k ((a,env), (PlusK b, env):stk)
          ((PlusK (LitE m), env), (LitE n, _env'):stk) ->
              k ((LitE (m+n), env), stk)
          _ -> error $ "TODO: " ++ show s

--------------------------------------------------------------------------------

e1 :: Exp
e1 = AppE (LamE (VarE 0)) (LitE 32)

t1 :: KMR
t1 = k ((e1, Env []), [])

e2 :: Exp
e2 = AppE (LamE (PlusE (VarE 0) (LitE 10))) (LitE 32)

t2 :: KMR
t2 = k ((e2, Env []), [])

e3 :: Exp
e3 = AppE (LamE (SuccE (SuccE (SuccE (VarE 0))))) (LitE 10)

t3 :: KMR
t3 = k ((e3, Env []), [])

e4 :: Exp
e4 = AppE (LamE (PlusE (VarE 0) (LitE 32))) (LitE 10)

t4 :: KMR
t4 = k ((e4, Env []), [])

e5 :: Exp
e5 = PlusE (PlusE (LitE 5) (LitE 32)) (LitE 5)

t5 :: KMR
t5 = k ((e4, Env []), [])

--------------------------------------------------------------------------------
