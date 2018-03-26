module CLS where

import Debug.Trace

data Exp = VarE Var
         | LamE Exp
         | AppE Exp Exp
         | LitE Int
         | SuccE Exp
         | SuccK
         | PlusE Exp Exp
         | PlusK Exp
         | Ap -- tag
  deriving (Read, Show, Eq, Ord)

newtype Env = Env [Clos]
  deriving (Read, Show, Eq, Ord)

popenv :: Env -> Clos
popenv (Env clos) = head clos

appenv :: Env -> Env -> Env
appenv (Env a) (Env b) = Env (a++b)

type Var  = Int

type Clos = (Exp,Env)

cls :: [Exp] -> [Env] -> [Clos] -> Clos
cls exps envs stk =
  case (exps,envs,stk) of
    ([],_,v:_) -> v
    (e@LitE{}:c, l, s) -> cls c l ((e,Env s):s)
    (LamE bod:c, e:l, s) -> cls c l ((bod,e):s)
    (AppE f a:c, e:l, s) -> cls (f:a:Ap:c) (e:e:l) s
    (VarE 0:c, (Env v):l, s) -> cls c l (v ++ s)
    (VarE n:c, e:l, s) -> cls (VarE (n-1):c) l s
    (Ap:c, e1:l, (t,e):s) -> cls (t:c) ((appenv e1 e):l) s
    oth -> error $ show oth

e1 :: Exp
e1 = (LitE 32)
t1 = cls [e1] [Env []] []


e2 :: Exp
e2 = (LamE (VarE 0))
t2 = cls [e2] [Env []] []

e3 :: Exp
e3 = AppE (LamE (VarE 0)) (LitE 10)
t3 = cls [e3] [Env []] []
