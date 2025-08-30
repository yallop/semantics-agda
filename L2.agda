{-# OPTIONS --without-K --guardedness --safe --exact-split #-}

open import Data.Nat hiding (_+_)
open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Locations
𝕃 : Set
𝕃 = ℕ

-- Operations
data Op : Set where
  + ≥ : Op

-- Types
data Type : Set where
  int bool unit : Type
  _➝_ : Type → Type → Type

infixr 20 _➝_

➝-t₂-injective : ∀ { t₁ t₂ t₁' t₂'} → (t₁ ➝ t₂) ≡ (t₁' ➝ t₂') → t₂ ≡ t₂'
➝-t₂-injective refl = refl

➝-t₁-injective : ∀ { t₁ t₂ t₁' t₂'} → (t₁ ➝ t₂) ≡ (t₁' ➝ t₂') → t₁ ≡ t₁'
➝-t₁-injective refl = refl

≡-type : (x y : Type) → Dec (x ≡ y)
≡-type int int = yes refl
≡-type int bool = no λ ()
≡-type int unit = no λ ()
≡-type int (t₁ ➝ t₂) = no λ ()
≡-type bool int = no λ ()
≡-type bool bool = yes refl
≡-type bool unit = no λ ()
≡-type bool (t₁ ➝ t₂) = no λ ()
≡-type unit int = no λ ()
≡-type unit bool = no λ ()
≡-type unit unit = yes refl
≡-type unit (t₁ ➝ t₂) = no λ ()
≡-type (t₁ ➝ t₂) int = no λ ()
≡-type (t₁ ➝ t₂) bool = no λ ()
≡-type (t₁ ➝ t₂) unit = no λ ()
≡-type (t₁ ➝ t₂) (t₁' ➝ t₂') with (≡-type t₁ t₁') | (≡-type t₂ t₂')
... | yes refl | yes refl = yes refl
... | yes refl | no p = no λ q → p (➝-t₂-injective q)
... | no p | _ = no λ q → p (➝-t₁-injective q)

-- Variables
𝕏 : Set
𝕏 = ℕ

-- Grammar
data Expression : Set where
  N : ℤ → Expression
  B : Bool → Expression
  _[_]_ : Expression → Op → Expression → Expression
  If_Then_Else_ : Expression → Expression → Expression → Expression
  _:=_ : 𝕃 → Expression → Expression
  !_ : 𝕃 → Expression
  Skip : Expression
  _⨾_ : Expression → Expression → Expression
  While_Do_  : Expression → Expression → Expression
  _＠_ : Expression → Expression → Expression -- This is function application
  Fn:_⇒_ : Type → Expression → Expression
  Var : 𝕏 → Expression
  LetVal:_≔_In_ : Type → Expression → Expression → Expression
  LetValRec:_➝_≔[Fn:_⇒_]In_ : Type → Type → Type → Expression → Expression → Expression

infixl 60 _＠_
infix 50 !_
infix 50 Var
infix 40 _[_]_
infix 30 _:=_
infix 20 While_Do_
infix 20 If_Then_Else_
infixl 10 _⨾_
infix 0 Fn:_⇒_
infixl 0 LetVal:_≔_In_
infixl 0 LetValRec:_➝_≔[Fn:_⇒_]In_

data Value : Expression → Set where
  value-N : ∀ {n} → Value (N n)
  value-B : ∀ {b} → Value (B b)
  value-skip : Value Skip
  value-Fn : ∀ {T e} → Value (Fn: T ⇒ e)

-- Store
Store : Set
Store = List (Maybe ℤ)

_↦_ : 𝕃 → ℤ → Store
(zero ↦ z) = just z ∷ []
(suc n ↦ z) = nothing ∷ (n ↦ z)

Ø : Store
Ø = Data.List.[]

_⨄_ : Store → Store → Store
[] ⨄ l = l
(x ∷ l) ⨄ [] = x ∷ l
(_ ∷ l₁) ⨄ (just v ∷ l₂) = just v ∷ (l₁ ⨄ l₂)
(v ∷ l₁) ⨄ (nothing ∷ l₂) = v ∷ (l₁ ⨄ l₂)

infixl 20 _⨄_

_!!_ : Store → 𝕃 → Maybe ℤ
[] !! ℓ = nothing
(v ∷ _) !! zero = v
(_ ∷ s) !! suc ℓ = s !! ℓ

--  Substitution
σ = List Expression

lookup : σ → 𝕏 → Maybe (Expression)
lookup [] x = nothing
lookup (y ∷ es) zero = just y
lookup (y ∷ es) (suc n) = lookup es n

ρ : Set
ρ = 𝕏 → 𝕏

rename : ρ → Expression → Expression
rename r (N n) = N n
rename r (B b) = B b
rename r (e₁ [ op ] e₂) = (rename r e₁) [ op ] (rename r e₂)
rename r (If e₁ Then e₂ Else e₃) = If (rename r e₁) Then (rename r e₂) Else (rename r e₃)
rename r (l := e) = l := (rename r e)
rename r (! l) = ! l
rename r Skip = Skip
rename r (e₁ ⨾ e₂) = (rename r e₁) ⨾ (rename r e₂)
rename r (While e₁ Do e₂) = While (rename r e₁) Do (rename r e₂)
rename r (e₁ ＠ e₂) = (rename r e₁) ＠ (rename r e₂)
rename r (Fn: T ⇒ e) = Fn: T ⇒ (rename r e)
rename r (Var x) = Var (r x)
rename r (LetVal: T ≔ e₁ In e₂) = LetVal: T ≔ (rename r e₁) In (rename r e₂)
rename r (LetValRec: T₁ ➝ T₂ ≔[Fn: T₃ ⇒ e₁ ]In e₂) = LetValRec: T₁ ➝ T₂ ≔[Fn: T₃ ⇒ (rename r e₁) ]In (rename r e₂)

↑ : Expression → Expression
↑ = rename suc

≥2?+1 : ρ
≥2?+1 zero = zero
≥2?+1 (suc zero) = suc zero
≥2?+1 (2+ n) = suc (2+ n)

≥2?↑ : Expression → Expression
≥2?↑ = rename ≥2?+1

shift : σ → ℕ → σ
shift s zero = s
shift s (suc n) = (Var 0) ∷ map (↑) (shift s n)

⇑ : σ → σ
⇑ s = shift s 1

swap : ρ
swap zero = suc (zero)
swap (suc zero) = zero
swap (2+ n) = 2+ n

⇄ : Expression → Expression
⇄ e = rename swap e


subst :  σ → Expression → Expression
subst s (N n) = N n
subst s (B b) = B b
subst s (e₁ [ op ] e₂) = (subst s e₁) [ op ] (subst s e₂)
subst s (If e₁ Then e₂ Else e₃) = If (subst s e₁) Then (subst s e₂) Else (subst s e₃)
subst s (l := e) = l := (subst s e)
subst s (! l) = ! l
subst s Skip = Skip
subst s (e₁ ⨾ e₂) = (subst s e₁) ⨾ (subst s e₂)
subst s (While e₁ Do e₂) = While (subst s e₁) Do (subst s e₂)
subst s (e₁ ＠ e₂) = (subst s e₁) ＠ (subst s e₂)
subst s (Fn: T ⇒ e) = Fn: T ⇒ subst (⇑ s) e
subst s (Var x) with lookup s x
... | just e = e
... | nothing = Var x
subst s (LetVal: T ≔ e₁ In e₂) = LetVal: T ≔ subst s e₁ In subst (⇑ s) e₂
subst s (LetValRec: T₁ ➝ T₂ ≔[Fn: T₃ ⇒ e₁ ]In e₂) = LetValRec: T₁ ➝ T₂ ≔[Fn: T₃ ⇒ subst (⇑ (⇑ s)) e₁ ]In subst (⇑ s) e₂

-- Operational Semantics
data _⟶_ : Expression × Store → Expression × Store → Set where

  op+ : ∀ {n₁ n₂ s} →
        ⟨ N n₁ [ + ] N n₂ , s ⟩ ⟶ ⟨ N (n₁ +ℤ n₂) , s ⟩

  op≥ : ∀ {n₁ n₂ s} →
        ⟨ N n₁ [ ≥ ] N n₂ , s ⟩ ⟶ ⟨ B (n₂ ≤ℤ n₁) , s ⟩

  op1 : ∀ {e₁ op e₂ s e₁' s'} →
       ⟨ e₁ , s ⟩ ⟶ ⟨ e₁' , s' ⟩  →
       ------------------------------------------
       ⟨ e₁ [ op ] e₂ , s ⟩ ⟶ ⟨ e₁' [ op ] e₂ , s' ⟩

  op2 : ∀ {v e₂ s e₂' s' op} →
       Value v →
       ⟨ e₂ , s ⟩ ⟶ ⟨ e₂' , s' ⟩  →
       ------------------------------------------
       ⟨ v [ op ] e₂ , s ⟩ ⟶ ⟨ v [ op ] e₂' , s' ⟩

  deref : ∀ {ℓ n s} →
       (s !! ℓ ≡ just n) →
       ⟨ ! ℓ , s ⟩ ⟶ ⟨ N n , s ⟩

  assign1 : ∀ {ℓ m n s} →
       s !! ℓ ≡ just m →
       ⟨ ℓ := N n , s ⟩ ⟶ ⟨ Skip , s ⨄ (ℓ ↦ n) ⟩

  assign2 : ∀ {ℓ e s e' s'} →
       ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ →
      --------------------------------
       ⟨ ℓ := e , s ⟩ ⟶ ⟨ ℓ := e' , s' ⟩

  seq1 : ∀ {e₂ s} →
       ⟨ Skip ⨾ e₂ , s ⟩ ⟶ ⟨ e₂ , s ⟩

  seq2 : ∀ {e₁ e₂ s e₁' s'} →
       ⟨ e₁ , s ⟩ ⟶ ⟨ e₁' , s' ⟩ →
      --------------------------------
       ⟨ e₁ ⨾ e₂ , s ⟩ ⟶ ⟨ e₁' ⨾ e₂ , s' ⟩

  if1 : ∀ {e₂ e₃ s} →
      ⟨ If B true Then e₂ Else e₃ , s ⟩ ⟶ ⟨ e₂ , s ⟩

  if2 : ∀ {e₂ e₃ s} →
      ⟨ If B false Then e₂ Else e₃ , s ⟩ ⟶ ⟨ e₃ , s ⟩

  if3 : ∀ {e₁ e₂ e₃ s e₁' s'} →
      ⟨ e₁ , s ⟩ ⟶ ⟨ e₁' , s' ⟩ →
      -----------------------------------------------------------
      ⟨ If e₁ Then e₂ Else e₃ , s ⟩ ⟶ ⟨ If e₁' Then e₂ Else e₃ , s' ⟩

  while : ∀ {e₁ e₂ s} →
      ⟨ While e₁ Do e₂ , s ⟩ ⟶ ⟨ If e₁ Then (e₂ ⨾ (While e₁ Do e₂)) Else Skip , s ⟩

  app1 : ∀ { e₁ e₂ e₁' s s' } →
      ⟨ e₁ , s ⟩ ⟶ ⟨ e₁' , s' ⟩ →
      ----------------------------------
      ⟨ e₁ ＠ e₂ , s ⟩ ⟶ ⟨ e₁' ＠ e₂ , s' ⟩

  app2 : ∀ { v e₂ e₂' s s' } →
      Value v →
      ⟨ e₂ , s ⟩ ⟶ ⟨ e₂' , s' ⟩ →
      ----------------------------------
      ⟨ v ＠ e₂ , s ⟩ ⟶ ⟨ v ＠ e₂' , s' ⟩

  fn : ∀ { v e s T } →
      Value v →
      ----------------------------------
      ⟨ (Fn: T ⇒ e) ＠ v , s ⟩ ⟶ ⟨ (subst (v ∷ []) e) , s ⟩

  let1 :  ∀ { e₁ e₂ e₁' s s' T } →
    ⟨ e₁ , s ⟩ ⟶ ⟨ e₁' , s' ⟩ →
    -------------------------------
    ⟨ LetVal: T ≔ e₁ In e₂ , s ⟩ ⟶ ⟨ LetVal: T ≔ e₁' In e₂ , s' ⟩

  let2 :  ∀ { v e s T } →
    Value v →
    -------------------------------
    ⟨ LetVal: T ≔ v In e , s ⟩ ⟶ ⟨ subst (v ∷ []) e , s ⟩

  letrecfn : ∀ { e₁ e₂ s T₁ T₂ } →
    ⟨ LetValRec: T₁ ➝ T₂ ≔[Fn: T₁ ⇒ e₁ ]In e₂ , s ⟩ ⟶
    ⟨ subst ((Fn: T₁ ⇒ LetValRec: T₁ ➝ T₂  ≔[Fn: T₁ ⇒ ≥2?↑ e₁ ]In (⇄ e₁)) ∷ []) e₂ , s ⟩


data _⟶⋆_ : Expression × Store → Expression × Store → Set where
  · : ∀ {e s} → ⟨ e , s ⟩ ⟶⋆ ⟨ e , s ⟩
  _then_ : ∀ {e s e' s' e'' s''} →
          ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ →
          ⟨ e' , s' ⟩ ⟶⋆ ⟨ e'' , s'' ⟩ →
          ⟨ e , s ⟩ ⟶⋆ ⟨ e'' , s'' ⟩

_⟶⋆∘_ : ∀ {e₁ e₂ e₃ s₁ s₂ s₃} →
       ⟨ e₁ , s₁ ⟩ ⟶⋆ ⟨ e₂ , s₂ ⟩ →
       ⟨ e₂ , s₂ ⟩ ⟶⋆ ⟨ e₃ , s₃ ⟩ →
       ⟨ e₁ , s₁ ⟩ ⟶⋆ ⟨ e₃ , s₃ ⟩
· ⟶⋆∘ r = r
(r then rs) ⟶⋆∘ rs' = r then (rs ⟶⋆∘ rs')

infixr 5 _then_

data Tloc : Set where
  intref : Tloc

StoreEnv : Set
StoreEnv = 𝕃 → Maybe Tloc

TypeEnv : Set
TypeEnv = 𝕏 → Maybe Type

• : TypeEnv
• = λ {n → nothing}

_,_ : TypeEnv → Type → TypeEnv
Γ , T = λ { zero → just T; (suc n) → Γ (n) }

infixl 5 _,_

data _⨾_⊢_∶_ : StoreEnv → TypeEnv → Expression → Type → Set where
  int : ∀ { Σ Γ n} →
      Σ ⨾ Γ ⊢ N n ∶ int

  bool : ∀ { Σ Γ b } →
      Σ ⨾ Γ ⊢ B b ∶ bool

  op+ : ∀ { Σ Γ e₁ e₂ } →
     Σ ⨾ Γ ⊢ e₁ ∶ int →
     Σ ⨾ Γ ⊢ e₂ ∶ int →
     --------------------
     Σ ⨾ Γ ⊢ e₁ [ + ] e₂ ∶ int

  op≥ : ∀ { Σ Γ e₁ e₂ } →
     Σ ⨾ Γ ⊢ e₁ ∶ int →
     Σ ⨾ Γ ⊢ e₂ ∶ int →
     ---------------------
     Σ ⨾ Γ ⊢ e₁ [ ≥ ] e₂ ∶ bool

  if : ∀ { Σ Γ e₁ e₂ e₃ T } →
     Σ ⨾ Γ ⊢ e₁ ∶ bool →
     Σ ⨾ Γ ⊢ e₂ ∶ T →
     Σ ⨾ Γ ⊢ e₃ ∶ T →
     -------------------------------
     Σ ⨾ Γ ⊢ If e₁ Then e₂ Else e₃ ∶ T

  assign : ∀ { Σ Γ ℓ e } →
     Σ (ℓ) ≡ just intref →
     Σ ⨾ Γ ⊢ e ∶ int →
     -----------------
     Σ ⨾ Γ ⊢ ℓ := e ∶ unit

  deref : ∀ { Σ Γ ℓ } →
     Σ (ℓ) ≡ just intref →
     -------------------
     Σ ⨾ Γ ⊢ ! ℓ ∶ int

  skip : ∀ { Σ Γ } →
     Σ ⨾ Γ ⊢ Skip ∶ unit

  seq : ∀ { Σ Γ e₁ e₂ T } →
     Σ ⨾ Γ ⊢ e₁ ∶ unit →
     Σ ⨾ Γ ⊢ e₂ ∶ T →
     --------------
     Σ ⨾ Γ ⊢ e₁ ⨾ e₂ ∶ T

  while : ∀ { Σ Γ e₁ e₂} →
     Σ ⨾ Γ ⊢ e₁ ∶ bool →
     Σ ⨾ Γ ⊢ e₂ ∶ unit →
     ------------------------
     Σ ⨾ Γ ⊢ While e₁ Do e₂ ∶ unit

  var : ∀ { Σ Γ x T } →
    Γ ( x ) ≡ just T →
    ------------------------
    Σ ⨾ Γ ⊢ Var x ∶ T

  fn : ∀ { Σ Γ T₁ T₂ e } →
    Σ ⨾ (Γ , T₁) ⊢ e ∶ T₂ →
    ------------------------
    Σ ⨾ Γ ⊢ (Fn: T₁ ⇒ e) ∶ (T₁ ➝ T₂)

  app : ∀ { Σ Γ T₁ T₂ e₁ e₂ } →
    Σ ⨾ Γ ⊢ e₁ ∶ (T₁ ➝ T₂) →
    Σ ⨾ Γ ⊢ e₂ ∶ T₁ →
    ------------------------
    Σ ⨾ Γ ⊢ e₁ ＠ e₂ ∶ T₂

  letval : ∀ { Σ Γ T₁ T₂ e₁ e₂ } → -- This corresponds to the "let" rule in the notes,
                                   -- Naming restrictions prevent me from naming it such
    Σ ⨾ Γ ⊢ e₁ ∶ T₁ →
    Σ ⨾ ( Γ , T₁ ) ⊢ e₂ ∶ T₂ →
    ------------------------
    Σ ⨾ Γ ⊢ LetVal: T₁ ≔ e₁ In e₂ ∶ T₂

  letrecfn : ∀ { Σ Γ T₁ T₂ T e₁ e₂ } →
    Σ ⨾ ( (Γ , ( T₁ ➝ T₂ ), T₁)) ⊢ e₁ ∶ T₂ →
    Σ ⨾ ( Γ , ( T₁ ➝ T₂ ) ) ⊢ e₂ ∶ T →
    ------------------------
    Σ ⨾ Γ ⊢ LetValRec: T₁ ➝ T₂ ≔[Fn: T₁ ⇒ e₁ ]In e₂ ∶ T
