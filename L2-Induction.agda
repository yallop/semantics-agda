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

data IH_at_⨾_⊢_∶_ (P : TypeEnv → Expression → Type → Set) : StoreEnv → TypeEnv → Expression → Type → Set where
  int : ∀ {Σ Γ n} →
      IH P at Σ ⨾ Γ ⊢ N n ∶ int

  bool : ∀ {Σ Γ b} →
      IH P at Σ ⨾ Γ ⊢ B b ∶ bool

  op+ : ∀ {Σ Γ e₁ e₂} →
     P Γ e₁ int →
     P Γ e₂ int →
     --------------------
     IH P at Σ ⨾ Γ ⊢ e₁ [ + ] e₂ ∶ int

  op≥ : ∀ {Σ Γ e₁ e₂} →
     P Γ e₁ int →
     P Γ e₂ int →
     ---------------------
     IH P at Σ ⨾ Γ ⊢ e₁ [ ≥ ] e₂ ∶ bool

  if : ∀ {Σ Γ e₁ e₂ e₃ T} →
     P Γ e₁ bool →
     P Γ e₂ T →
     P Γ e₃ T →
     -------------------------------
     IH P at Σ ⨾ Γ ⊢ If e₁ Then e₂ Else e₃ ∶ T

  assign : ∀ {Σ Γ ℓ e} →
     Σ (ℓ) ≡ just intref →
     P Γ e int →
     -----------------
     IH P at Σ ⨾ Γ ⊢ ℓ := e ∶ unit

  deref : ∀ {Σ Γ ℓ} →
     Σ (ℓ) ≡ just intref →
     -------------------
     IH P at Σ ⨾ Γ ⊢ ! ℓ ∶ int

  skip : ∀ {Σ Γ} →
     IH P at Σ ⨾ Γ ⊢ Skip ∶ unit

  seq : ∀ {Σ Γ e₁ e₂ T} →
     P Γ e₁ unit →
     P Γ e₂ T →
     --------------
     IH P at Σ ⨾ Γ ⊢ e₁ ⨾ e₂ ∶ T

  while : ∀ {Σ Γ e₁ e₂} →
     P Γ e₁ bool →
     P Γ e₂ unit →
     ------------------------
     IH P at Σ ⨾ Γ ⊢ While e₁ Do e₂ ∶ unit

  var : ∀ { Σ Γ x T } →
    Γ ( x ) ≡ just T →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ Var x ∶ T

  fn : ∀ { Σ Γ T₁ T₂ e } →
    P (Γ , T₁) e T₂ →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ (Fn: T₁ ⇒ e) ∶ (T₁ ➝ T₂)

  app : ∀ { Σ Γ T₁ T₂ e₁ e₂ } →
    P Γ e₁ (T₁ ➝ T₂) →
    P Γ e₂ T₁ →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ e₁ ＠ e₂ ∶ T₂

  letval : ∀ { Σ Γ T₁ T₂ e₁ e₂ } →
    P Γ e₁ T₁ →
    P (Γ , T₁) e₂ T₂ →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ LetVal: T₁ ≔ e₁ In e₂ ∶ T₂

  letrecfn : ∀ { Σ Γ T₁ T₂ T e₁ e₂ } →
    P (Γ , ( T₁ ➝ T₂ ), T₁) e₁ T₂ →
    P ( Γ , ( T₁ ➝ T₂ ) ) e₂ T →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ LetValRec: T₁ ➝ T₂ ≔[Fn: T₁ ⇒ e₁ ]In e₂ ∶ T

⊢-induction : ∀ {Σ Γ e T} →
    ∀ {P : TypeEnv → Expression → Type → Set} →
    (∀ {Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → IH P at Σ ⨾ Γ ⊢ e ∶ T → P Γ e T) →
    (Σ ⨾ Γ ⊢ e ∶ T) →
    P Γ e T
⊢-induction k te@int = k te int      -- te stands for typed expression, is an alias for int
⊢-induction k te@bool = k te bool
⊢-induction k te@(op+ e₁ e₂) = k te (op+ (⊢-induction k e₁) (⊢-induction k e₂))
⊢-induction k te@(op≥ e₁ e₂) = k te (op≥ (⊢-induction k e₁) (⊢-induction k e₂))
⊢-induction k te@(if e₁ e₂ e₃) = k te (if (⊢-induction k e₁) (⊢-induction k e₂) (⊢-induction k e₃))
⊢-induction k te@(assign l e) = k te (assign l (⊢-induction k e))
⊢-induction k te@(deref l) = k te (deref l)
⊢-induction k te@skip = k te skip
⊢-induction k te@(seq e₁ e₂) = k te (seq (⊢-induction k e₁) (⊢-induction k e₂))
⊢-induction k te@(while e₁ e₂) = k te (while (⊢-induction k e₁) (⊢-induction k e₂))
⊢-induction k te@(var x) = k te (var x)
⊢-induction k te@(fn e) = k te (fn (⊢-induction k e))
⊢-induction k te@(app e₁ e₂) = k te (app (⊢-induction k e₁) (⊢-induction k e₂))
⊢-induction k te@(letval e₁ e₂) = k te (letval (⊢-induction k e₁) (⊢-induction k e₂))
⊢-induction k te@(letrecfn e₁ e₂) = k te (letrecfn (⊢-induction k e₁) (⊢-induction k e₂))
