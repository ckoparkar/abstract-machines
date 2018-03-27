module CLS where

-- import Debug.Trace

data Exp = VarE Var
         | LamE Exp
         | AppE Exp Exp
         | LitE Int
         | SuccE Exp
         | SuccK -- tag
         | Ap -- tag
  deriving (Read, Show, Eq, Ord)

newtype Env = Env [Clos]
  deriving (Read, Show, Eq, Ord)

appenv :: Clos -> Env -> Env
appenv a (Env b) = Env (a:b)

type Var  = Int

type Clos = (Exp,Env)

cls :: [Exp] -> [Env] -> [Clos] -> Clos
cls exps envs stk =
  case (exps,envs,stk) of
    ([],_,v:_) -> v
    (expr@LitE{}:c, e:l      , s)            -> cls c l ((expr,e):s)
    (LamE bod:c   , e:l      , s)            -> cls c l ((bod,e):s)
    (AppE f a:c   , e:l      , s)            -> cls (f:a:Ap:c) (e:e:l) s
    (VarE 0:c     , (Env v):l, s)            -> cls c l (v ++ s)
    (VarE n:c     , e:l      , s)            -> cls (VarE (n-1):c) (e:l) s
    (Ap:c         , l        , v:(t,e):s)    -> cls (t:c) ((appenv v e):l) s
    (SuccE expr:c , e:l      , s)            -> cls (expr:SuccK:c) (e:l) s
    (SuccK:c      , l        , (LitE n,e):s) -> cls c l ((LitE (n+1),e):s)
    oth -> error $ show oth

e1 :: Exp
e1 = (LitE 32)

t1 :: Clos
t1 = cls [e1] [Env []] []


e2 :: Exp
e2 = (LamE (VarE 0))

t2 :: Clos
t2 = cls [e2] [Env []] []

e3 :: Exp
e3 = AppE (LamE (SuccE (VarE 0))) (LitE 10)

t3 :: Clos
t3 = cls [e3] [Env []] []
