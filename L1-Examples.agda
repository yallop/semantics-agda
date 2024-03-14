{-# OPTIONS --without-K --guardedness --safe --exact-split #-}

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_)
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import L1
open import L1-Theorems


ℓ ℓ₀ ℓ₁ ℓ₂ ℓ₃ : 𝕃
ℓ = 1000
ℓ₀ = 0
ℓ₁ = 1
ℓ₂ = 2
ℓ₃ = 3

slide-22-expression : Expression
slide-22-expression = (ℓ₂ := N 0ℤ) ؛
           (While ((! ℓ₁) [ ≥ ] (N (+_ 1))) Do (
              (ℓ₂ := ((! ℓ₂) [ + ] (! ℓ₁))) ؛
              (ℓ₁ := ((! ℓ₁) [ + ] N -1ℤ))
           ))

slide-22-store : Store
slide-22-store = (Ø ⨄ (ℓ₁ ↦ +_ 3)) ⨄ (ℓ₂ ↦ +_ 0)
slide-28-reduction-1 : ⟨ (N (+_ 2) [ + ] N (+_ 3)) [ + ] (N (+_ 6) [ + ] N (+_ 7)) , Ø ⟩ ⟶ ⟨ N (+_ 5) [ + ] (N (+_ 6) [ + ] N (+_ 7)) , Ø ⟩
slide-28-reduction-1 = op1 op+

slide-28-reduction-2 : ⟨ N (+_ 5) [ + ] (N (+_ 6) [ + ] N (+_ 7)) , Ø ⟩ ⟶ ⟨ N (+_ 5) [ + ] N (+_ 13) , Ø ⟩
slide-28-reduction-2 = op2 value-N op+

slide-28-reduction-3 : ⟨ N (+_ 5) [ + ] N (+_ 13) , Ø ⟩ ⟶ ⟨ N (+_ 18) , Ø ⟩
slide-28-reduction-3 = op+


slide-30-reduction-1 : ⟨ ℓ := N (+_ 3) ؛ ! ℓ , Ø ⨄ (ℓ ↦ +_ 0) ⟩ ⟶⋆ ⟨ N (+_ 3) , Ø ⨄ (ℓ ↦ +_ 3) ⟩
slide-30-reduction-1 = seq2 (assign1 refl) then
                       seq1 then
                       (deref refl) then ·

slide-30-reduction-2 : ⟨ ℓ := N (+_ 3) ؛ ℓ := ! ℓ , Ø ⨄ (ℓ ↦ +_ 0) ⟩ ⟶⋆ ⟨ Skip , Ø ⨄ (ℓ ↦ +_ 3) ⟩ -- This one is not in the lecture notes
slide-30-reduction-2 = seq2 (assign1 refl) then
                       seq1 then assign2 (deref refl) then
                       assign1 refl then ·

-- Note, this example is a proof that the expression ⟨ N (+_ 15) [ + ] ! ℓ , Ø ⟩ is not reducible

slide-30-reduction-3 : ∀ {e s} → ¬ (⟨ N (+_ 15) [ + ] ! ℓ , Ø ⟩ ⟶ ⟨ e , s ⟩)
slide-30-reduction-3 (op2 value-N (deref ()))

-- my made-up example to check that non-termination proofs are represented correctly

nt : Expression
nt = While (B true) Do Skip

-- nt-doesn't-terminate : ⟨ nt , [] ⟩ →ω
-- nt-doesn't-terminate = while and-then (if1 and-then (seq1 and-then nt-doesn't-terminate))
open _→ω
nt→ω : ⟨ nt , [] ⟩ →ω
c' nt→ω = ⟨ nt , [] ⟩
step₁ nt→ω = while then if1 then seq1 then ·
steps nt→ω = nt→ω
