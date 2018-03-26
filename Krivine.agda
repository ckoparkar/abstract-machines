module Krivine where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat
open import Data.String hiding (_≟_)
open import Data.Maybe
open import Data.Sum
open import Data.List hiding (_++_)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------

data Typ : Set where
  num : Typ
  str : Typ
  _⇒_ : Typ → Typ → Typ

data Exp : Set where
  Var   : ℕ → Exp
  Num   : ℕ → Exp
  Succ  : Exp -> Exp
  Str   : String → Exp
  Plus  : Exp → Exp → Exp
  Times : Exp → Exp → Exp
  Cat   : Exp → Exp → Exp
  Len   : Exp → Exp
  Let   : Exp → Exp → Exp
  Lam   : Exp → Exp
  App   : Exp → Exp → Exp

------------------------------------------------------------------------------
-- Static Semantics

data Ctxt : Set where
  □   : Ctxt
  _,_ : (ℕ × Typ) → Ctxt → Ctxt

data _∈_ : (ℕ × Typ) → Ctxt → Set where
  here : ∀ {Γ s τ} → (s , τ) ∈ ((s , τ) , Γ)
  skip : ∀ {Γ s τ s' τ'} →
         {α : False (s ≟ s')} → (s , τ) ∈ Γ → (s , τ) ∈ ((s' , τ') , Γ)

data _⊢_∷_ : (Γ : Ctxt) → (e : Exp) → (τ : Typ) → Set where
  VarT   : ∀ {Γ s τ} →
             ((s , τ) ∈ Γ) →
             ---------------
             Γ ⊢ Var s ∷ τ

  -- StrT   : ∀ {Γ s} →
  --            ----------------
  --            Γ ⊢ Str s ∷ str

  NumT   : ∀ {Γ n} →
             ----------------
             Γ ⊢ Num n ∷ num

  SuccT   : ∀ {Γ e} →
              (Γ ⊢ e ∷ num) →
              ---------------
              (Γ ⊢ Succ e ∷ num)

  -- PlusT  : ∀ {Γ e₁ e₂} →
  --            (Γ ⊢ e₁ ∷ num) → (Γ ⊢ e₂ ∷ num) →
  --            --------------------------------
  --                Γ ⊢ (Plus e₁ e₂) ∷ num

  LamT   : ∀ {Γ s e τ₁ τ₂} →
           (((s , τ₁) , Γ) ⊢ e ∷ τ₂) →
           --------------------------------------------
           (Γ ⊢ (Lam e) ∷ (τ₁ ⇒ τ₂))

  AppT   : ∀ {Γ e₁ e₂ τ τ₂} →
           (Γ ⊢ e₁ ∷ (τ₂ ⇒ τ)) → (Γ ⊢ e₂ ∷ τ₂) →
           -------------------------------------------------------
           (Γ ⊢ App e₁ e₂ ∷ τ)

------------------------------------------------------------------------------
-- Dynamic Semantics

data Env : Set

Val : Set

data isVal : Exp → Set where
  VNum : {n : ℕ} → isVal (Num n)
  -- VStr : {s : String} → isVal (Str s)
  VLam : {e : Exp} -> Env -> isVal (Lam e)

Val = Σ[ e ∈ Exp ] isVal e

vnum : ℕ → Val
vnum n = Num n , VNum

-- vstr : String → Val
-- vstr s = Str s , VStr

vlam : Exp -> Env -> Val
vlam bod ρ = Lam bod , VLam ρ

--

data Env where
  □   : Env
  _,_ : (ℕ × Val) → Env → Env

data _∈ᵣ_ : (ℕ × Val) → Env → Set where
  hereᵣ : ∀ {ρ s v} → (s , v) ∈ᵣ ((s , v) , ρ)
  skipᵣ : ∀ {ρ s v s' v'} →
         {α : False (s ≟ s')} → (s , v) ∈ᵣ ρ → (s , v) ∈ᵣ ((s' , v') , ρ)

--

Closure : Set
Closure = Exp × Env


data Frame : Set where
  SuccK : Frame
  AppLK : Closure -> Frame
  AppRK : Val -> Frame

Stack : Set
Stack = List Frame

data State : Set where
  Enter  : Closure -> Stack -> State
  Return : Stack -> Val -> State

data _↦_ : State -> State -> Set where
  NumE : ∀ {n ρ stk} -> (Enter (Num n , ρ) stk) ↦ Return stk (vnum n)
  VarE : ∀ {x v ρ stk} -> ((x , v) ∈ᵣ ρ)
         -> (Enter (Var x , ρ) stk) ↦ (Return stk v)
  SuccE : ∀ {e ρ stk}
          -> (Enter (Succ e , ρ) stk) ↦ (Enter (e , ρ) (SuccK ∷ stk))
  SuccK : ∀ {stk n}
          -> (Return (SuccK ∷ stk) (Num n , VNum)) ↦ Return stk (vnum (n + 1))
  LamE : ∀ {bod ρ stk}
         -> (Enter (Lam bod , ρ) stk) ↦ (Return stk (vlam bod ρ))
  AppE : ∀ {fn arg ρ stk}
         -> (Enter (App fn arg , ρ) stk) ↦ (Enter (fn , ρ) (AppLK (arg , ρ) ∷ stk))
  AppK : ∀ {arg ρ k fn} ->
         (Return (AppLK (arg , ρ) ∷ k) fn) ↦ (Enter (arg , ρ) (AppRK fn ∷ k))
  AppS : ∀ {env k v bod arg} ->
         (Return (AppRK (Lam bod , VLam env) ∷ k) arg) ↦
         (Enter (bod , ((v , arg) , env)) k)

--------------------------------------------------------------------------------

infixr 10 _•_

data _↦*_ : State → State → Set where
  ∎   : ∀ {s} → s ↦* s
  _•_ : ∀ {s₁ s₂ s₃} → s₁ ↦ s₂ → s₂ ↦* s₃ → s₁ ↦* s₃

--

Eval : Exp → Val → Set
Eval e v = (Enter (e , □) []) ↦* (Return [] v)

-- Example

e1 : Exp
e1 = Num 1

t1 : Eval e1 (vnum 1)
t1 = NumE • ∎

e2 : Exp
e2 = Succ (Num 1)

t2 : Eval e2 (vnum 2)
t2 = SuccE • (NumE • SuccK • ∎)

e3 : Exp
e3 = App (Lam (Var 0)) (Num 32)

t3 : Eval e3 (vnum 32)
t3 = AppE • (LamE • (AppK • (NumE • (AppS • (VarE hereᵣ) • ∎))))

--------------------------------------------------------------------------------

-- Type safety

-- When is a value compatible with a type v ∼ τ

data _≈_ : Env → Ctxt -> Set

data _∼_ : Val → Typ → Set where
  num∼ : ∀ {n} → (Num n , VNum) ∼ num
  -- str∼ : ∀ {s} → (Str s , VStr) ∼ str
  lam∼ : ∀ {s e ρ Γ τ₁ τ₂} →
           (ρ ≈ Γ) → (((s , τ₁) , Γ) ⊢ e ∷ τ₂) →
           (vlam e ρ) ∼ (τ₁ ⇒ τ₂)

-- When is a runtime environment compatible with a typing context ρ ≈ Γ

data _≈_ where
  □≈ : □ ≈ □
  x≈ : ∀ {x y v τ ρ Γ} →
       x ≡ y → v ∼ τ → ρ ≈ Γ → ((x , v) , ρ) ≈ ((y , τ) , Γ)

Γ⇒v : ∀ {x τ Γ ρ} →
      ρ ≈ Γ → ((x , τ) ∈ Γ) → Σ[ v ∈ Val ] (x , v) ∈ᵣ ρ
Γ⇒v □≈ ()
Γ⇒v (x≈ refl v∼τ ρ≈Γ) here = _ , hereᵣ
Γ⇒v (x≈ refl v∼τ ρ≈Γ) (skip {α = α} inΓ) =
  let (v , inρ) = Γ⇒v ρ≈Γ inΓ in v , skipᵣ {α = α} inρ

ρ⇒vτ : ∀ {x τ v Γ ρ} →
       ρ ≈ Γ → ((x , v) ∈ᵣ ρ) → ((x , τ) ∈ Γ) → v ∼ τ
ρ⇒vτ □≈ ()
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) hereᵣ here = v∼τ
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) hereᵣ (skip {α = α} inΓ) =
  ⊥-elim (toWitnessFalse α refl)
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) (skipᵣ {α = α} inρ) here =
  ⊥-elim (toWitnessFalse α refl)
ρ⇒vτ (x≈ refl v∼τ ρ≈Γ) (skipᵣ inρ) (skip inΓ) = ρ⇒vτ ρ≈Γ inρ inΓ

-- Closure typing cl ⊢c τ

_⊢c_ : Closure → Typ → Set
(e , ρ) ⊢c τ = Σ[ Γ ∈ Ctxt ] (ρ ≈ Γ × Γ ⊢ e ∷ τ)

extend : Closure → ℕ → Val → Closure
extend (e , ρ) x v = (e , ((x , v) , ρ))

--------------------------------------------------------------------------------

-- Frame typing fr ⊢f (τ , τ)

data _⊢f_ : Frame → (Typ × Typ) → Set where
  AppLKT : ∀ {cl a b}
           -> cl ⊢c a
           -> (AppLK cl) ⊢f (a ⇒ b , b)

  AppRKT : ∀ {fn a b}
           -- -> (∀ {v1} → (v1 ∼ a) → extend cl x v1 ⊢c b)
           -> fn ∼ (a ⇒ b)
           -> AppRK fn ⊢f (a , b)

-- Continuation typing κ ⊢κ (τ , τ)

data _⊢κ_ : Stack → (Typ × Typ) → Set where
  EmptyKT : ∀ {τ} →
    [] ⊢κ (τ , τ)
  PushKT  : ∀ {fr κ τ₁ τ₂ τ₃} →
    fr ⊢f (τ₁ , τ₂) →
    κ ⊢κ (τ₂ , τ₃) →
    (fr ∷ κ) ⊢κ (τ₁ , τ₃)

-- State typing

data _⊢s_ : State → Typ → Set where
  EnterT  : ∀ {cl κ τ₁ τ₂} →
    cl ⊢c τ₁ →
    κ ⊢κ (τ₁ , τ₂) →
    (Enter cl κ) ⊢s τ₂
  ReturnT : ∀ {κ v τ₁ τ₂} →
    κ ⊢κ (τ₁ , τ₂) →
    v ∼ τ₁ →
    Return κ v ⊢s τ₂

-- Initial and final states

loadT : ∀ {e τ} → (□ ⊢ e ∷ τ) → (Enter (e , □) []) ⊢s τ
loadT et = EnterT (□ , □≈ , et) EmptyKT

data Final : State → Typ → Set where
  F : ∀ {v τ} → (v ∼ τ) → Final (Return [] v) τ

-- Progress
-- If we are well-typed and not final then we can make some progress

progress : ∀ {s τ} → s ⊢s τ → (Final s τ) ⊎ (Σ[ s' ∈ State ] s ↦ s')
progress (ReturnT EmptyKT v∼τ) = inj₁ (F v∼τ)
progress (EnterT (Γ , ρ≈Γ , VarT inΓ) κt) =
  inj₂ (_ , VarE (proj₂ (Γ⇒v ρ≈Γ inΓ)))
progress (EnterT (Γ , ρ≈Γ , NumT) κt) = inj₂ (_ , NumE)
progress (EnterT (Γ , ρ≈Γ , LamT proj₆) kt) = inj₂ (_ , LamE)
progress (EnterT (Γ , ρ≈Γ , AppT fn arg) kt) = inj₂ (_ , AppE)
progress (ReturnT (PushKT (AppLKT x) kt) v=t) = inj₂ (_ , AppK)
progress (EnterT (proj₄ , proj₅ , SuccT proj₆) x) = inj₂ (_ , SuccE)
progress (ReturnT (PushKT (AppRKT x2) x₃) x₄) = inj₂ ({!!} , {!!})

preservation : ∀ {s s' τ} → s ↦ s' → s ⊢s τ → s' ⊢s τ
preservation (VarE inρ) (EnterT (Γ , ρ≈Γ , VarT inΓ) κt) =
  ReturnT κt (ρ⇒vτ ρ≈Γ inρ inΓ)
preservation NumE (EnterT (Γ , ρ≈Γ , NumT) κt) = ReturnT κt num∼
preservation SuccK = {!!}
preservation LamE (EnterT (Γ , ρ≈Γ , LamT lam) kt) = ReturnT kt (lam∼ ρ≈Γ lam)
preservation AppE (EnterT (Γ , ρ≈Γ , AppT fn arg) kt) =
  EnterT (Γ , ρ≈Γ , fn) (PushKT (AppLKT (Γ , ρ≈Γ , arg)) kt)
preservation AppK (ReturnT (PushKT (AppLKT (Γ , ρ≈Γ , arg)) kt) vt) =
  EnterT (Γ , ρ≈Γ , arg) (PushKT (AppRKT vt) kt)
preservation AppS (ReturnT (PushKT (AppRKT (lam∼ ρ≈Γ lam)) kt) vt) =
  EnterT ({!!} , ((x≈ {!!} {!!} {!!}) , {!!})) kt
  -- EnterT ({!!} , x≈ refl vt ρ≈Γ , lam) kt
preservation SuccE (EnterT (proj₃ , proj₄ , SuccT proj₅) x) = {!!}
