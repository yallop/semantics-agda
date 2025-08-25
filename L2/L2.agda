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
  Var_ : 𝕏 → Expression
  LetVal:_≔_In_ : Type → Expression → Expression → Expression
  LetValRec:_➝_≔[Fn:_⇒_]In_ : Type → Type → Type → Expression → Expression → Expression

infixl 60 _＠_ 
infix 50 !_
infix 50 Var_
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
 
