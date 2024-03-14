{-# OPTIONS --without-K --guardedness --safe --exact-split #-}

open import Data.Nat hiding (_+_)
open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)


𝕃 : Set
𝕃 = ℕ

data Op : Set where
  + ≥ : Op

data Expression : Set where
  N : ℤ → Expression
  B : Bool → Expression
  _[_]_ : Expression → Op → Expression → Expression
  If_Then_Else_ : Expression → Expression → Expression → Expression
  _:=_ : 𝕃 → Expression → Expression
  !_ : 𝕃 → Expression
  Skip : Expression
  _؛_ : Expression → Expression → Expression
  While_Do_  : Expression → Expression → Expression

infix 50 !_
infix 40 _[_]_
infix 30 _:=_
infix 20 While_Do_
infix 20 If_Then_Else_
infixl 10 _؛_

data Value : Expression → Set where
  value-N : ∀ {n} → Value (N n)
  value-B : ∀ {b} → Value (B b)
  value-skip : Value Skip

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
       ⟨ Skip ؛ e₂ , s ⟩ ⟶ ⟨ e₂ , s ⟩

  seq2 : ∀ {e₁ e₂ s e₁' s'} →
       ⟨ e₁ , s ⟩ ⟶ ⟨ e₁' , s' ⟩ →
      --------------------------------
       ⟨ e₁ ؛ e₂ , s ⟩ ⟶ ⟨ e₁' ؛ e₂ , s' ⟩

  if1 : ∀ {e₂ e₃ s} →
      ⟨ If B true Then e₂ Else e₃ , s ⟩ ⟶ ⟨ e₂ , s ⟩

  if2 : ∀ {e₂ e₃ s} →
      ⟨ If B false Then e₂ Else e₃ , s ⟩ ⟶ ⟨ e₃ , s ⟩

  if3 : ∀ {e₁ e₂ e₃ s e₁' s'} →
      ⟨ e₁ , s ⟩ ⟶ ⟨ e₁' , s' ⟩ →
      -----------------------------------------------------------
      ⟨ If e₁ Then e₂ Else e₃ , s ⟩ ⟶ ⟨ If e₁' Then e₂ Else e₃ , s' ⟩

  while : ∀ {e₁ e₂ s} →
      ⟨ While e₁ Do e₂ , s ⟩ ⟶ ⟨ If e₁ Then (e₂ ؛ (While e₁ Do e₂)) Else Skip , s ⟩

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

data Type : Set where
  int bool unit : Type

≡-type : (x y : Type) → Dec (x ≡ y)
≡-type int  int  = yes refl
≡-type bool bool = yes refl
≡-type unit unit = yes refl
≡-type int  bool = no λ ()
≡-type int  unit = no λ ()
≡-type bool int  = no λ ()
≡-type bool unit = no λ ()
≡-type unit int  = no λ ()
≡-type unit bool = no λ ()

data Tloc : Set where
  intref : Tloc

TypeEnv : Set
TypeEnv = 𝕃 → Maybe Tloc

data _⊢_∶_ : TypeEnv → Expression → Type → Set where
  int : ∀ {Γ n} →
      Γ ⊢ N n ∶ int

  bool : ∀ {Γ b} →
      Γ ⊢ B b ∶ bool

  op+ : ∀ {Γ e₁ e₂} →
     Γ ⊢ e₁ ∶ int →
     Γ ⊢ e₂ ∶ int →
     --------------------
     Γ ⊢ e₁ [ + ] e₂ ∶ int

  op≥ : ∀ {Γ e₁ e₂} →
     Γ ⊢ e₁ ∶ int →
     Γ ⊢ e₂ ∶ int →
     ---------------------
     Γ ⊢ e₁ [ ≥ ] e₂ ∶ bool

  if : ∀ {Γ e₁ e₂ e₃ T} →
     Γ ⊢ e₁ ∶ bool →
     Γ ⊢ e₂ ∶ T →
     Γ ⊢ e₃ ∶ T →
     -------------------------------
     Γ ⊢ If e₁ Then e₂ Else e₃ ∶ T

  assign : ∀ {Γ ℓ e} →
     Γ (ℓ) ≡ just intref →
     Γ ⊢ e ∶ int →
     -----------------
     Γ ⊢ ℓ := e ∶ unit

  deref : ∀ {Γ ℓ} →
     Γ (ℓ) ≡ just intref →
     -------------------
     Γ ⊢ ! ℓ ∶ int

  skip : ∀ {Γ} →
     Γ ⊢ Skip ∶ unit

  seq : ∀ {Γ e₁ e₂ T} →
     Γ ⊢ e₁ ∶ unit →
     Γ ⊢ e₂ ∶ T →
     --------------
     Γ ⊢ e₁ ؛ e₂ ∶ T

  while : ∀ {Γ e₁ e₂} →
     Γ ⊢ e₁ ∶ bool →
     Γ ⊢ e₂ ∶ unit →
     ------------------------
     Γ ⊢ While e₁ Do e₂ ∶ unit
