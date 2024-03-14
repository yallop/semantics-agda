{-# OPTIONS --without-K --guardedness --safe --exact-split #-}

open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import L1

data _at_ (P : Expression → Set) : Expression → Set where
  N : (z : ℤ) → P at N z
  B : (b : Bool) → P at B b
  _[_]_ : ∀ {l r} → P l → (op : Op) → P r → P at (l [ op ] r)
  If_Then_Else_ : ∀ {c t e} → P c → P t → P e → P at (If c Then t Else e)
  _:=_ : ∀ {e} → (ℓ : 𝕃) → P e → P at (ℓ := e)
  !_ : (ℓ : 𝕃) → P at (! ℓ)
  Skip : P at Skip
  _؛_ : ∀ {l r} → P l → P r → P at (l ؛ r)
  While_Do_ : ∀ {l r} → P l → P r → P at (While l Do r)

structural-induction :
  {P : Expression → Set} →
  (∀ {l : Expression} → P at l → P l) →
  (l : Expression) → P l
structural-induction k (N x) = k (N x)
structural-induction k (B x) = k (B x)
structural-induction k (e [ x ] e₁) = k (structural-induction k e [ x ] structural-induction k e₁)
structural-induction k (If e Then e₁ Else e₂) = k (If (structural-induction k e)
                                                Then (structural-induction k e₁)
                                                Else (structural-induction k e₂))
structural-induction k (x := e) = k ((x := structural-induction k e))
structural-induction k (! x) = k ( ! x)
structural-induction k Skip = k Skip
structural-induction k (e ؛ e₁) = k ((structural-induction k e ؛ structural-induction k  e₁))
structural-induction k (While e Do e₁) = k (While (structural-induction k e) Do (structural-induction k e₁))

data _at_⊢_∶_ (P : Expression → Type → Set) : TypeEnv → Expression → Type → Set where
  int : ∀ {Γ n} →
      P at Γ ⊢ N n ∶ int

  bool : ∀ {Γ b} →
      P at Γ ⊢ B b ∶ bool

  op+ : ∀ {Γ e₁ e₂} →
     P e₁ int →
     P e₂ int →
     --------------------
     P at Γ ⊢ e₁ [ + ] e₂ ∶ int

  op≥ : ∀ {Γ e₁ e₂} →
     P e₁ int →
     P e₂ int →
     ---------------------
     P at Γ ⊢ e₁ [ ≥ ] e₂ ∶ bool

  if : ∀ {Γ e₁ e₂ e₃ T} →
     P e₁ bool →
     P e₂ T →
     P e₃ T →
     -------------------------------
     P at Γ ⊢ If e₁ Then e₂ Else e₃ ∶ T

  assign : ∀ {Γ ℓ e} →
     Γ (ℓ) ≡ just intref →
     P e int →
     -----------------
     P at Γ ⊢ ℓ := e ∶ unit

  deref : ∀ {Γ ℓ} →
     Γ (ℓ) ≡ just intref →
     -------------------
     P at Γ ⊢ ! ℓ ∶ int

  skip : ∀ {Γ} →
     P at Γ ⊢ Skip ∶ unit

  seq : ∀ {Γ e₁ e₂ T} →
     P e₁ unit →
     P e₂ T →
     --------------
     P at Γ ⊢ e₁ ؛ e₂ ∶ T

  while : ∀ {Γ e₁ e₂} →
     P e₁ bool →
     P e₂ unit →
     ------------------------
     P at Γ ⊢ While e₁ Do e₂ ∶ unit

⊢-induction :
  -- NB: none of the typing rules changes the typing environment
  -- so we don't need to quantify it internally.
  -- This simplifies proofs significantly, avoiding the need 
  -- to quantify over dom⊆ Γ s in the instantiation of P in Progress,
  -- for example
  ∀ {Γ e τ} → 
  {P : Expression → Type → Set} →
  (∀ {e τ} → Γ ⊢ e ∶ τ → P at Γ ⊢ e ∶ τ → P e τ) →
   Γ ⊢ e ∶ τ                   → P e τ
⊢-induction k p@int = k p int
⊢-induction k p@bool = k p bool
⊢-induction k p@(op+ d d₁) = k p (op+ (⊢-induction k d) (⊢-induction k d₁))
⊢-induction k p@(op≥ d d₁) = k p (op≥ (⊢-induction k d) (⊢-induction k d₁))
⊢-induction k p@(if d d₁ d₂) = k p (if (⊢-induction k d) (⊢-induction k d₁) (⊢-induction k d₂))
⊢-induction k p@(assign x d) = k p (assign x (⊢-induction k d))
⊢-induction k p@(deref x) = k p (deref x)
⊢-induction k p@skip = k p skip
⊢-induction k p@(seq d d₁) = k p (seq (⊢-induction k d) (⊢-induction k d₁))
⊢-induction k p@(while d d₁) = k p (while (⊢-induction k d) (⊢-induction k d₁))


data _at_⟶_ (P : Expression × Store → Expression × Store → Set)
                   : Expression × Store → Expression × Store → Set where

  op+ : ∀ {n₁ n₂ s} →
        P at ⟨ N n₁ [ + ] N n₂ , s ⟩ ⟶ ⟨ N (n₁ +ℤ n₂) , s ⟩

  op≥ : ∀ {n₁ n₂ s} →
        P at ⟨ N n₁ [ ≥ ] N n₂ , s ⟩ ⟶ ⟨ B (n₂ ≤ℤ n₁) , s ⟩

  op1 : ∀ {e₁ op e₂ s e₁' s'} →
       P ⟨ e₁ , s ⟩ ⟨ e₁' , s' ⟩  →
       ------------------------------------------
       P at ⟨ e₁ [ op ] e₂ , s ⟩ ⟶ ⟨ e₁' [ op ] e₂ , s' ⟩

  op2 : ∀ {v e₂ s e₂' s' op} →
       Value v →
       P ⟨ e₂ , s ⟩ ⟨ e₂' , s' ⟩  →
       ------------------------------------------
       P at ⟨ v [ op ] e₂ , s ⟩ ⟶ ⟨ v [ op ] e₂' , s' ⟩

  deref : ∀ {ℓ n s} →
       (s !! ℓ ≡ just n) →
       P at ⟨ ! ℓ , s ⟩ ⟶ ⟨ N n , s ⟩

  assign1 : ∀ {ℓ m n s} →
       s !! ℓ ≡ just m →
       P at ⟨ ℓ := N n , s ⟩ ⟶ ⟨ Skip , s ⨄ (ℓ ↦ n) ⟩

  assign2 : ∀ {ℓ e s e' s'} →
       P ⟨ e , s ⟩ ⟨ e' , s' ⟩ →
      --------------------------------
       P at ⟨ ℓ := e , s ⟩ ⟶ ⟨ ℓ := e' , s' ⟩

  seq1 : ∀ {e₂ s} →
       P at ⟨ Skip ؛ e₂ , s ⟩ ⟶ ⟨ e₂ , s ⟩

  seq2 : ∀ {e₁ e₂ s e₁' s'} →
       P ⟨ e₁ , s ⟩ ⟨ e₁' , s' ⟩ →
      --------------------------------
       P at ⟨ e₁ ؛ e₂ , s ⟩ ⟶ ⟨ e₁' ؛ e₂ , s' ⟩

  if1 : ∀ {e₂ e₃ s} →
      P at ⟨ If B true Then e₂ Else e₃ , s ⟩ ⟶ ⟨ e₂ , s ⟩

  if2 : ∀ {e₂ e₃ s} →
      P at ⟨ If B false Then e₂ Else e₃ , s ⟩ ⟶ ⟨ e₃ , s ⟩

  if3 : ∀ {e₁ e₂ e₃ s e₁' s'} →
      P ⟨ e₁ , s ⟩ ⟨ e₁' , s' ⟩ →
      -----------------------------------------------------------
      P at ⟨ If e₁ Then e₂ Else e₃ , s ⟩ ⟶ ⟨ If e₁' Then e₂ Else e₃ , s' ⟩

  while : ∀ {e₁ e₂ s} →
      P at ⟨ While e₁ Do e₂ , s ⟩ ⟶ ⟨ If e₁ Then (e₂ ؛ (While e₁ Do e₂)) Else Skip , s ⟩

→-induction :
  ∀ {e s e' s'} → 
  {P : Expression × Store → Expression × Store → Set} →
  (∀ {e s e' s'} → P at ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ → P ⟨ e , s ⟩ ⟨ e' , s' ⟩) →
  ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ →  P ⟨ e , s ⟩ ⟨ e' , s' ⟩
→-induction k op+ = k op+
→-induction k op≥ = k op≥
→-induction k (op1 x) = k (op1 (→-induction k x))
→-induction k (op2 x x₁) = k (op2 x (→-induction k x₁))
→-induction k (deref x) = k (deref x)
→-induction k (assign1 x) = k (assign1 x)
→-induction k (assign2 x) = k (assign2 (→-induction k x))
→-induction k seq1 = k seq1
→-induction k (seq2 x) = k (seq2 (→-induction k x))
→-induction k if1 = k if1
→-induction k if2 = k if2
→-induction k (if3 x) = k ((if3 (→-induction k x)))
→-induction k while = k while
