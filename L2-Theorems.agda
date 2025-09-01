{-# OPTIONS --safe --without-K --exact-split #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe renaming (map to maybeMap)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans) renaming (subst to ≡-subst)

open import L2
open import L2-Induction

data _⨟_⊨σ_∶_ (Σ : StoreEnv) (Γ' : TypeEnv) (s : σ)  (Γ : TypeEnv) : Set where
    compatible : (∀ {T} x → Γ(x) ≡ just T → Σ ⨾ Γ' ⊢ s x ∶ T) → Σ ⨟ Γ' ⊨σ s ∶ Γ

data _⊢ρ_∶_ (Γ' : TypeEnv) (r : ρ)  (Γ : TypeEnv)  : Set where
    compatible : (∀ x  → Γ' (r x) ≡ Γ(x)) → Γ' ⊢ρ r ∶ Γ

⇑ᵣ-equiv : ∀ {Γ Γ' r T} → Γ' ⊢ρ r ∶ Γ → (x : 𝕏) → (Γ' ,,, T) ((⇑ᵣ r) x) ≡ (Γ ,,, T) x
⇑ᵣ-equiv _ zero = refl
⇑ᵣ-equiv (compatible p) (suc x) = p x

⇑ᵣ-has-type : ∀ {Γ Γ' T r} → Γ' ⊢ρ r ∶ Γ → (Γ' ,,, T) ⊢ρ (⇑ᵣ r) ∶ (Γ ,,, T)
⇑ᵣ-has-type p = compatible (⇑ᵣ-equiv p)

Renaming : ∀ {Σ Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → ∀ {Γ' r} → {{Γ' ⊢ρ r ∶ Γ}} → Σ ⨾ Γ' ⊢ (rename r e) ∶ T
Renaming {Σ} derivation =  ⊢-induction-simple case derivation where
    P : TypeEnv → Expression → Type → Set
    P Γ e T =  ∀ {Γ' r} →  {{Γ' ⊢ρ r ∶ Γ}} → Σ ⨾ Γ' ⊢ (rename r e) ∶ T
    case : ∀ {Γ e T} → IH P at Σ ⨾ Γ ⊢ e ∶ T → (∀ {Γ' r} →  {{Γ' ⊢ρ r ∶ Γ}} → Σ ⨾ Γ' ⊢ (rename r e) ∶ T)
    case int                               = int
    case bool                              = bool
    case (op≥ h₁ h₂)                       = op≥ h₁ h₂
    case (op+ h₁ h₂)                       = op+ h₁ h₂
    case (if h₁ h₂ h₃)                     = if h₁ h₂ h₃
    case (assign ℓ h)                      = assign ℓ h
    case (deref ℓ)                         = deref ℓ
    case skip                              = skip
    case (seq h₁ h₂)                       = seq h₁ h₂
    case (while h₁ h₂)                     =  while h₁ h₂
    case (var x)          {{compatible p}} = var (trans (p _) x)
    case (fn h)           {{c}}            = fn (h {{⇑ᵣ-has-type c}})
    case (app h₁ h₂)                       = app h₁ h₂
    case (letval h₁ h₂)   {{c}}            = letval h₁ (h₂ {{⇑ᵣ-has-type c}})
    case (letrecfn h₁ h₂) {{c}}            = letrecfn (h₁ {{(⇑ᵣ-has-type (⇑ᵣ-has-type c)) }}) (h₂ {{⇑ᵣ-has-type c}})


⇑-has-type : ∀ {Σ Γ Γ' s T} → (Σ ⨟ Γ' ⊨σ s ∶ Γ) → (Σ ⨟ (Γ' ,,, T) ⊨σ ⇑ s ∶ (Γ ,,, T))
⇑-has-type {Σ} {Γ' = Γ'} {s} {T} (compatible p) = compatible (λ {
  zero T → var T;
  (suc x) T →(Renaming (p x T) {{compatible (λ _ → refl)}})})

-- Lemma 20: Substitution
Substitution : ∀ {Σ Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → (∀ {Γ' s} → {{Σ ⨟ Γ' ⊨σ s ∶ Γ}} → Σ ⨾ Γ' ⊢ subst s e ∶ T)
Substitution {Σ} deriv = ⊢-induction-simple case deriv where
    P : TypeEnv → Expression → Type → Set
    P Γ e T = ∀ {Γ' s} → {{Σ ⨟ Γ' ⊨σ s ∶ Γ}} → Σ ⨾ Γ' ⊢ subst s e ∶ T
    case : ∀ {Γ e T} → IH P at Σ ⨾ Γ ⊢ e ∶ T → P Γ e T
    case int                               = int
    case bool                              = bool
    case (op+ h₁ h₂)                       = op+ h₁ h₂
    case (op≥ h₁ h₂)                       = op≥ h₁ h₂
    case (if h₁ h₂ h₃)                     = if h₁ h₂ h₃
    case (assign ℓ h)                      = assign ℓ h
    case (deref ℓ)                         = deref ℓ
    case skip                              = skip
    case (seq h₁ h₂)                       = seq h₁ h₂
    case (while h₁ h₂)                     = while h₁ h₂
    case (var x)          {{compatible p}} = p _ x
    case (fn h)           {{c}}            = fn (h {{⇑-has-type c}})
    case (app h₁ h₂)                       = app h₁ h₂
    case (letval h₁ h₂)   {{c}}            = letval h₁ (h₂ {{⇑-has-type c}})
    case (letrecfn h₁ h₂) {{c}}            = letrecfn (h₁ {{⇑-has-type (⇑-has-type c)}}) (h₂ {{⇑-has-type c}})
