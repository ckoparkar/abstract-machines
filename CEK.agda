module CEK where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.String
open import Data.Maybe
open import Data.Sum
open import Data.List hiding (_++_)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------
-- This starter file only gives the semantics for a subset of the
-- language without higher-order functions. You should do the
-- development for the full language.

data Typ : Set where
  num : Typ
  str : Typ
  _⇒_ : Typ → Typ → Typ

data Exp : Set where
  Var   : String → Exp
  Num   : ℕ → Exp
  Str   : String → Exp
  Plus  : Exp → Exp → Exp
  Times : Exp → Exp → Exp
  Cat   : Exp → Exp → Exp
  Len   : Exp → Exp
  Let   : String → Exp → Exp → Exp
  Lam   : String → Exp → Exp
  App   : Exp → Exp → Exp

------------------------------------------------------------------------------
-- Static Semantics

data Ctxt : Set where
  □   : Ctxt
  _,_ : (String × Typ) → Ctxt → Ctxt

data _∈_ : (String × Typ) → Ctxt → Set where
  here : ∀ {Γ s τ} → (s , τ) ∈ ((s , τ) , Γ)
  skip : ∀ {Γ s τ s' τ'} →
         {α : False (s ≟ s')} → (s , τ) ∈ Γ → (s , τ) ∈ ((s' , τ') , Γ)

data _⊢_∷_ : (Γ : Ctxt) → (e : Exp) → (τ : Typ) → Set where
  VarT   : ∀ {Γ s τ} →
             ((s , τ) ∈ Γ) →
             ---------------
             Γ ⊢ Var s ∷ τ
  StrT   : ∀ {Γ s} →
             ----------------
             Γ ⊢ Str s ∷ str
  NumT   : ∀ {Γ n} →
             ----------------
             Γ ⊢ Num n ∷ num
  PlusT  : ∀ {Γ e₁ e₂} →
             (Γ ⊢ e₁ ∷ num) → (Γ ⊢ e₂ ∷ num) →
             --------------------------------
                 Γ ⊢ (Plus e₁ e₂) ∷ num
  TimesT : ∀ {Γ e₁ e₂} →
             (Γ ⊢ e₁ ∷ num) → (Γ ⊢ e₂ ∷ num) →
             ---------------------------------
                 Γ ⊢ (Times e₁ e₂) ∷ num
  CatT   : ∀ {Γ e₁ e₂} →
             (Γ ⊢ e₁ ∷ str) → (Γ ⊢ e₂ ∷ str) →
             ---------------------------------
                 Γ ⊢ (Cat e₁ e₂) ∷ str
  LenT   : ∀ {Γ e} →
             (Γ ⊢ e ∷ str) →
             ---------------
             (Γ ⊢ Len e ∷ num)
  LetT   : ∀ {Γ s e₁ e₂ τ₁ τ₂} →
             (Γ ⊢ e₁ ∷ τ₁) → (((s , τ₁) , Γ) ⊢ e₂ ∷ τ₂) →
             ------------------------------------------
                      Γ ⊢ Let s e₁ e₂ ∷ τ₂

  LamT   : ∀ {Γ s e τ₁ τ₂} →
           (((s , τ₁) , Γ) ⊢ e ∷ τ₂) →
           --------------------------------------------
           (Γ ⊢ (Lam s e) ∷ (τ₁ ⇒ τ₂))

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
  VStr : {s : String} → isVal (Str s)
  VLam : {s : String} -> {e : Exp} -> Env -> isVal (Lam s e)

Val = Σ[ e ∈ Exp ] isVal e

vnum : ℕ → Val
vnum n = Num n , VNum

vstr : String → Val
vstr s = Str s , VStr

vlam : String -> Exp -> Env -> Val
vlam s bod ρ = Lam s bod , VLam ρ

--

data Env where
  □   : Env
  _,_ : (String × Val) → Env → Env

data _∈ᵣ_ : (String × Val) → Env → Set where
  hereᵣ : ∀ {ρ s v} → (s , v) ∈ᵣ ((s , v) , ρ)
  skipᵣ : ∀ {ρ s v s' v'} →
         {α : False (s ≟ s')} → (s , v) ∈ᵣ ρ → (s , v) ∈ᵣ ((s' , v') , ρ)

--

Closure : Set
Closure = Exp × Env

--

data Frame : Set where
  PlusLK  : Closure → Frame
  TimesLK : Closure → Frame
  CatLK   : Closure → Frame
  LenK    : Frame
  LetK    : String → Closure → Frame
  PlusRK  : Val → Frame
  TimesRK : Val → Frame
  CatRK   : Val → Frame
  AppLK   : Closure -> Frame
  AppRK   : Val -> Frame

--

Cont : Set
Cont = List Frame

--

data State : Set where
  Enter  : Closure → Cont → State
  Return : Cont → Val → State

--

data _↦_ : State → State → Set where
  VarE   : ∀ {x v ρ κ} → ((x , v) ∈ᵣ ρ) →
    (Enter (Var x , ρ) κ) ↦ (Return κ v)
  NumE   : ∀ {n ρ κ} →
    (Enter (Num n , ρ) κ) ↦ (Return κ (vnum n))
  StrE   : ∀ {s ρ κ} →
    (Enter (Str s , ρ) κ) ↦ (Return κ (vstr s))
  PlusE  : ∀ {e₁ e₂ ρ κ} →
    (Enter (Plus e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (PlusLK (e₂ , ρ) ∷ κ))
  TimesE : ∀ {e₁ e₂ ρ κ} →
    (Enter (Times e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (TimesLK (e₂ , ρ) ∷ κ))
  CatE   : ∀ {e₁ e₂ ρ κ} →
    (Enter (Cat e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (CatLK (e₂ , ρ) ∷ κ))
  LenE   : ∀ {e ρ κ} →
    (Enter (Len e , ρ) κ) ↦ (Enter (e , ρ) (LenK ∷ κ))
  LetE   : ∀ {x e₁ e₂ ρ κ} →
    (Enter (Let x e₁ e₂ , ρ) κ) ↦ (Enter (e₁ , ρ) (LetK x (e₂ , ρ) ∷ κ))
  PlusK  : ∀ {e₂ ρ κ v} →
    (Return (PlusLK (e₂ , ρ) ∷ κ) v) ↦ (Enter (e₂ , ρ) (PlusRK v ∷ κ))
  TimesK : ∀ {e₂ ρ κ v} →
    (Return (TimesLK (e₂ , ρ) ∷ κ) v) ↦ (Enter (e₂ , ρ) (TimesRK v ∷ κ))
  CatK   : ∀ {e₂ ρ κ v} →
    (Return (CatLK (e₂ , ρ) ∷ κ) v) ↦ (Enter (e₂ , ρ) (CatRK v ∷ κ))
  LenS   : ∀ {κ s} →
    (Return (LenK ∷ κ) (Str s , VStr)) ↦ (Return κ (vnum (length (toList s))))
  LetS   : ∀ {x e₂ ρ κ v} →
    (Return (LetK x (e₂ , ρ) ∷ κ) v) ↦ (Enter (e₂ , (x , v) , ρ) κ)
  PlusS  : ∀ {m n κ} →
    (Return (PlusRK (Num m , VNum) ∷ κ) (Num n , VNum)) ↦
         (Return κ (vnum (m + n)))
  TimesS : ∀ {m n κ} →
    (Return (TimesRK (Num m , VNum) ∷ κ) (Num n , VNum)) ↦
         (Return κ (vnum (m * n)))
  CatS   : ∀ {s t κ} →
    (Return (CatRK (Str s , VStr) ∷ κ) (Str t , VStr)) ↦
         (Return κ (vstr (s ++ t)))
  LamE   : ∀ {s ρ κ bod} →
    (Enter (Lam s bod , ρ) κ) ↦ (Return κ (vlam s bod ρ))
  AppE : ∀ {fn arg ρ k} ->
    (Enter (App fn arg , ρ) k) ↦ (Enter (fn , ρ) (AppLK (arg , ρ) ∷ k))
  AppK : ∀ {arg ρ k fn} ->
         (Return (AppLK (arg , ρ) ∷ k) fn) ↦ (Enter (arg , ρ) (AppRK fn ∷ k))
  AppS : ∀ {env k v bod arg} ->
         (Return (AppRK (Lam v bod , VLam env) ∷ k) arg) ↦
         (Enter (bod , ((v , arg) , env)) k)

--

infixr 10 _•_

data _↦*_ : State → State → Set where
  ∎   : ∀ {s} → s ↦* s
  _•_ : ∀ {s₁ s₂ s₃} → s₁ ↦ s₂ → s₂ ↦* s₃ → s₁ ↦* s₃

--

Eval : Exp → Val → Set
Eval e v = (Enter (e , □) []) ↦* (Return [] v)

-- Example

e : Exp
e = Let "y" (Num 1) (Let "x" (Let "y" (Num 2) (Var "y")) (Var "y"))

tr : Eval e (vnum 1)
tr = LetE • NumE • LetS • LetE • LetE • NumE • LetS • VarE hereᵣ •
     LetS • VarE (skipᵣ hereᵣ) • ∎

------------------------------------------------------------------------------
-- Type safety

-- When is a value compatible with a type v ∼ τ

data _≈_ : Env → Ctxt -> Set

data _∼_ : Val → Typ → Set where
  num∼ : ∀ {n} → (Num n , VNum) ∼ num
  str∼ : ∀ {s} → (Str s , VStr) ∼ str
  lam∼ : ∀ {s e ρ Γ τ₁ τ₂} →
           (ρ ≈ Γ) → (((s , τ₁) , Γ) ⊢ e ∷ τ₂) →
           (vlam s e ρ) ∼ (τ₁ ⇒ τ₂)

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

extend : Closure → String → Val → Closure
extend (e , ρ) x v = (e , ((x , v) , ρ))

-- Frame typing fr ⊢f (τ , τ)

data _⊢f_ : Frame → (Typ × Typ) → Set where
  PlusLKT : ∀ {cl} →
    cl ⊢c num →
    (PlusLK cl) ⊢f (num , num)
  TimesLKT : ∀ {cl} →
    cl ⊢c num →
    (TimesLK cl) ⊢f (num , num)
  CatLKT : ∀ {cl} →
    cl ⊢c str →
    (CatLK cl) ⊢f (str , str)
  LenKT :
    LenK ⊢f (str , num)
  LetKT : ∀ {x cl τ₁ τ₂} →
    (∀ {v₁} → (v₁ ∼ τ₁) → extend cl x v₁ ⊢c τ₂) →
    LetK x cl ⊢f (τ₁ , τ₂)
  PlusRKT : ∀ {v} →
    (v ∼ num) →
    PlusRK v ⊢f (num , num)
  TimesRKT : ∀ {v} →
    (v ∼ num) →
    TimesRK v ⊢f (num , num)
  CatRKT : ∀ {v} →
    (v ∼ str) →
    CatRK v ⊢f (str , str)

  AppLKT : ∀ {cl a b}
           -> cl ⊢c a
           -> (AppLK cl) ⊢f (a ⇒ b , b)

  AppRKT : ∀ {fn a b}
           -- -> (∀ {v1} → (v1 ∼ a) → extend cl x v1 ⊢c b)
           -> fn ∼ (a ⇒ b)
           -> AppRK fn ⊢f (a , b)

-- Continuation typing κ ⊢κ (τ , τ)

data _⊢κ_ : Cont → (Typ × Typ) → Set where
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
progress (EnterT (Γ , ρ≈Γ , VarT inΓ) κt) =
  inj₂ (_ , VarE (proj₂ (Γ⇒v ρ≈Γ inΓ)))
progress (EnterT (Γ , ρ≈Γ , StrT) κt) = inj₂ (_ , StrE)
progress (EnterT (Γ , ρ≈Γ , NumT) κt) = inj₂ (_ , NumE)
progress (EnterT (Γ , ρ≈Γ , PlusT et₁ et₂) κt) = inj₂ (_ , PlusE)
progress (EnterT (Γ , ρ≈Γ , TimesT et₁ et₂) κt) = inj₂ (_ , TimesE)
progress (EnterT (Γ , ρ≈Γ , CatT et₁ et₂) κt) = inj₂ (_ , CatE)
progress (EnterT (Γ , ρ≈Γ , LenT et) κt) = inj₂ (_ , LenE)
progress (EnterT (Γ , ρ≈Γ , LetT et₁ et₂) κt) = inj₂ (_ , LetE)
progress (ReturnT EmptyKT v∼τ) = inj₁ (F v∼τ)
progress (ReturnT (PushKT (PlusLKT clt) κt) v∼τ) = inj₂ (_ , PlusK)
progress (ReturnT (PushKT (TimesLKT clt) κt) v∼τ) = inj₂ (_ , TimesK)
progress (ReturnT (PushKT (CatLKT clt) κt) v∼τ) = inj₂ (_ , CatK)
progress (ReturnT (PushKT LenKT κt) str∼) = inj₂ (_ , LenS)
progress (ReturnT (PushKT (LetKT pclt) κt) v∼τ) = inj₂ (_ , LetS)
progress (ReturnT (PushKT (PlusRKT num∼) κt) num∼) = inj₂ (_ , PlusS)
progress (ReturnT (PushKT (TimesRKT num∼) κt) num∼) = inj₂ (_ , TimesS)
progress (ReturnT (PushKT (CatRKT str∼) κt) str∼) = inj₂ (_ , CatS)
progress (EnterT (Γ , ρ≈Γ , LamT proj₆) kt) = inj₂ (_ , LamE)
progress (EnterT (Γ , ρ≈Γ , AppT fn arg) kt) = inj₂ (_ , AppE)
progress (ReturnT (PushKT (AppLKT x) kt) v=t) = inj₂ (_ , AppK)
progress (ReturnT (PushKT (AppRKT x2) x₃) x₄) = inj₂ ({!!} , {!!})

-- Preservation
-- If we are well-typed and make a step then the next state is also
-- well-typed

preservation : ∀ {s s' τ} → s ↦ s' → s ⊢s τ → s' ⊢s τ
preservation (VarE inρ) (EnterT (Γ , ρ≈Γ , VarT inΓ) κt) =
  ReturnT κt (ρ⇒vτ ρ≈Γ inρ inΓ)
preservation NumE (EnterT (Γ , ρ≈Γ , NumT) κt) = ReturnT κt num∼
preservation StrE (EnterT (Γ , ρ≈Γ , StrT) κt) = ReturnT κt str∼
preservation PlusE (EnterT (Γ , ρ≈Γ , PlusT et₁ et₂) κt) =
  EnterT (Γ , ρ≈Γ , et₁) (PushKT (PlusLKT (Γ , ρ≈Γ , et₂)) κt)
preservation TimesE (EnterT (Γ , ρ≈Γ , TimesT et₁ et₂) κt) =
  EnterT (Γ , ρ≈Γ , et₁) (PushKT (TimesLKT (Γ , ρ≈Γ , et₂)) κt)
preservation CatE (EnterT (Γ , ρ≈Γ , CatT et₁ et₂) κt) =
  EnterT (Γ , ρ≈Γ , et₁) (PushKT (CatLKT (Γ , ρ≈Γ , et₂)) κt)
preservation LenE (EnterT (Γ , ρ≈Γ , LenT et) κt) =
  EnterT (Γ , ρ≈Γ , et) (PushKT LenKT κt)
preservation LetE (EnterT (Γ , ρ≈Γ , LetT et₁ et₂) κt) =
  EnterT
    (Γ , ρ≈Γ , et₁)
    (PushKT (LetKT (λ v∼τ → (_ , Γ) , x≈ refl v∼τ ρ≈Γ , et₂)) κt)
preservation PlusK (ReturnT (PushKT (PlusLKT (Γ , ρ≈Γ , et)) κt) vt) =
  EnterT (Γ , ρ≈Γ , et) (PushKT (PlusRKT vt) κt)
preservation TimesK (ReturnT (PushKT (TimesLKT (Γ , ρ≈Γ , et)) κt) vt) =
  EnterT (Γ , ρ≈Γ , et) (PushKT (TimesRKT vt) κt)
preservation CatK (ReturnT (PushKT (CatLKT (Γ , ρ≈Γ , et)) κt) vt) =
  EnterT (Γ , ρ≈Γ , et) (PushKT (CatRKT vt) κt)
preservation LenS (ReturnT (PushKT LenKT κt) vt) = ReturnT κt num∼
preservation LetS (ReturnT (PushKT (LetKT pclt) κt) vt) =
  EnterT (pclt vt) κt
preservation PlusS (ReturnT (PushKT (PlusRKT x) κt) vt) = ReturnT κt num∼
preservation TimesS (ReturnT (PushKT (TimesRKT x) κt) vt) = ReturnT κt num∼
preservation CatS (ReturnT (PushKT (CatRKT x) κt) vt) = ReturnT κt str∼
preservation LamE (EnterT (Γ , ρ≈Γ , LamT lam) kt) = ReturnT kt (lam∼ ρ≈Γ lam)
preservation AppE (EnterT (Γ , ρ≈Γ , AppT fn arg) kt) =
  EnterT (Γ , ρ≈Γ , fn) (PushKT (AppLKT (Γ , ρ≈Γ , arg)) kt)
preservation AppK (ReturnT (PushKT (AppLKT (Γ , ρ≈Γ , arg)) kt) vt) =
  EnterT (Γ , ρ≈Γ , arg) (PushKT (AppRKT vt) kt)
preservation AppS (ReturnT (PushKT (AppRKT (lam∼ ρ≈Γ lam)) kt) vt) =
  EnterT ({!!} , x≈ refl vt ρ≈Γ , lam) kt

-- Main theorem

-- If we are well-typed, then either
--   - we are final
--   - we can make a step and the next state has the same type
--   - we diverge (at least as far as Agda is concerned)

type-safety-step : ∀ {s τ} → s ⊢s τ →
  Final s τ ⊎ Σ[ s' ∈ State ] (s ↦ s' × s' ⊢s τ)
type-safety-step st with progress st
type-safety-step st | inj₁ f = inj₁ f
type-safety-step st | inj₂ (s' , step) =
  inj₂ (s' , step , preservation step st)

{-# TERMINATING #-}
type-safety-step* : ∀ {s τ} → s ⊢s τ →
                    Σ[ s' ∈ State ] (s ↦* s' × Final s' τ)
type-safety-step* st with type-safety-step st
... | inj₁ f = _ , ∎ , f
... | inj₂ (s' , step , s't) =
  let (sf , steps , f) = type-safety-step* s't
  in sf , step • steps , f

type-safety : ∀ {e τ} → (□ ⊢ e ∷ τ) → Σ[ v ∈ Val ] (Eval e v) × (v ∼ τ)
type-safety et with type-safety-step* (loadT et)
... | (Return [] v) , steps , F vτ = v , steps , vτ
