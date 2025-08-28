{-# OPTIONS --without-K --guardedness --safe --exact-split #-}

open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import L2

data IH_at_ (P : Expression → Set)  : (e : Expression) → Set where
    N : (z : ℤ) → IH P at N z
    B : (b : Bool) → IH P at B b
    _[_]_ : ∀ {l r} → P l → (op : Op) → P r → IH P at (l [ op ] r)
    If_Then_Else_ : ∀ {c t e} → P c → P t → P e → IH P at (If c Then t Else e)
    _:=_ : ∀ {e} → (ℓ : 𝕃) → P e → IH P at (ℓ := e)
    !_ : (ℓ : 𝕃) → IH P at (! ℓ)
    Skip : IH P at Skip
    _⨾_ : ∀ {l r} → P l → P r → IH P at (l ⨾ r)
    While_Do_ : ∀ {l r} → P l → P r → IH P at (While l Do r)
    _＠_ : ∀ {e₁ e₂} → P e₁ → P e₂ → IH P at (e₁ ＠ e₂) -- This is function application
    Fn:_⇒_ : ∀ {e} → (T : Type) → P e → IH P at (Fn: T ⇒ e)
    Var : (x : 𝕏) → IH P at (Var x)
    LetVal:_≔_In_ : ∀ {e₁ e₂} → (T : Type) → P e₁ → P e₂ → IH P at (LetVal: T ≔ e₁ In e₂)
    LetValRec:_➝_≔[Fn:_⇒_]In_ : ∀ {e₁ e₂} →  (T₁ : Type) → (T₂ : Type) → (T₃ : Type) → P e₁ → P e₂ → IH P at (LetValRec: T₁ ➝ T₂ ≔[Fn: T₃ ⇒ e₁ ]In e₂)

structural-induction : {P : Expression → Set} →
    (∀ {e} → IH P at e → P e ) →
    (e : Expression) → P e
structural-induction k (N z) = k (N z)
structural-induction k (B b) = k (B b)
structural-induction k (e₁ [ op ] e₂) = k ((structural-induction k e₁) [ op ] (structural-induction k e₂))
structural-induction k (If e₁ Then e₂ Else e₃) = k (If (structural-induction k e₁) Then (structural-induction k e₂) Else (structural-induction k e₃))
structural-induction k (ℓ := e) = k (ℓ := (structural-induction k e))
structural-induction k (! ℓ) = k (! ℓ)
structural-induction k Skip = k Skip
structural-induction k (e₁ ⨾ e₂) = k ((structural-induction k e₁) ⨾ (structural-induction k e₂))
structural-induction k (While e₁ Do e₂) = k (While (structural-induction k e₁) Do (structural-induction k e₂))
structural-induction k (e₁ ＠ e₂) = k ((structural-induction k e₁) ＠ (structural-induction k e₂))
structural-induction k (Fn: T ⇒ e) = k (Fn: T ⇒ (structural-induction k e))
structural-induction k (Var x) = k (Var x)
structural-induction k (LetVal: T ≔ e₁ In e₂) = k (LetVal: T ≔ (structural-induction k e₁) In (structural-induction k e₂))
structural-induction k (LetValRec: T₁ ➝ T₂ ≔[Fn: T₃ ⇒ e₁ ]In e₂) = k (LetValRec: T₁ ➝ T₂ ≔[Fn: T₃ ⇒ (structural-induction k e₁) ]In (structural-induction k e₂))
