{-# OPTIONS --guardedness --safe --exact-split --copatterns #-}

open import Data.Nat hiding (_+_)
open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to maybeMap)
open import Data.Empty
open import Data.List using (List; []; _∷_) renaming (map to listMap)
open import Data.Sum
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function.Base using (case_of_; id)

open import L2
open import L2-Induction

data _⊨σ_∶_ : TypeEnv → σ → TypeEnv → Set where
    compatible : {Γ' : TypeEnv} → {s : σ} → {Γ : TypeEnv} → (∀ {x T Σ} → Γ(x) ≡ just T → (_⨾_⊢_∶_ Σ Γ' (lookup-var s x) T)) → Γ' ⊨σ s ∶ Γ

data _⊢ρ_∶_ : TypeEnv → ρ → TypeEnv → Set where
    compatible : {Γ' : TypeEnv} → {r : ρ} → {Γ : TypeEnv} → (∀ {x T} → Γ(x) ≡ just T → (Γ' (r x) ≡ just T)) → Γ' ⊢ρ r ∶ Γ

↑-has-type : ∀ {Γ T} → (Γ , T) ⊢ρ suc ∶ Γ
↑-has-type = compatible id

⇑ᵣ-equiv : ∀ {Γ Γ' r x T T'} → Γ' ⊢ρ r ∶ Γ → (Γ , T') x ≡ just T → (Γ' , T') ((⇑ᵣ r) x) ≡ just T
⇑ᵣ-equiv {Γ} {Γ'} {r} {zero} {T} {T'} p q = q
⇑ᵣ-equiv {Γ} {Γ'} {r} {suc x} {T} {T'} (compatible x₁) q = x₁ q

⇑ᵣ-has-type : ∀ {Γ Γ' T r} → Γ' ⊢ρ r ∶ Γ → (Γ' , T) ⊢ρ (⇑ᵣ r) ∶ (Γ , T)
⇑ᵣ-has-type {Γ} {Γ'} {T} {r} p = compatible (λ {x} → ⇑ᵣ-equiv {x = x} p)

RenamingLemma : ∀ {Σ Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → ∀ {Γ' r} → Γ' ⊢ρ r ∶ Γ → Σ ⨾ Γ' ⊢ (rename r e) ∶ T
RenamingLemma {Σ} {_} {_} {_} derivation =  ⊢-induction case derivation where
    P : TypeEnv → Expression → Type → Set
    P Γ e T =  ∀ {Γ' r} →  Γ' ⊢ρ r ∶ Γ → Σ ⨾ Γ' ⊢ (rename r e) ∶ T
    case : ∀ {Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → IH P at Σ ⨾ Γ ⊢ e ∶ T → P Γ e T
    case int ih compat-proof = int
    case bool ih compat-proof = bool
    case (op≥ deriv₁ deriv₂) (op≥ ih-e₁ ih-e₂) compat-proof = op≥ (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (op+ deriv₁ deriv₂) (op+ ih-e₁ ih-e₂) compat-proof = op+ (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (if deriv₁ deriv₂ deriv₃) (if ih-e₁ ih-e₂ ih-e₃) compat-proof = if (ih-e₁ compat-proof) (ih-e₂ compat-proof) (ih-e₃ compat-proof)
    case (assign ℓ deriv) (assign ih-ℓ ih-e) compat-proof = assign ℓ (ih-e compat-proof)
    case (deref ℓ) ih compat-proof = deref ℓ
    case skip ih compat-proof = skip
    case (seq deriv₁ deriv₂) (seq ih-e₁ ih-e₂)  compat-proof = seq (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (while deriv₁ deriv₂) (while ih-e₁ ih-e₂)  compat-proof = while (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (var x) ih (compatible p) = var (p x)
    case (fn deriv) (fn ih-e) compat-proof = fn (ih-e (⇑ᵣ-has-type compat-proof))
    case (app deriv₁ deriv₂) (app ih-e₁ ih-e₂) compat-proof = app (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (letval deriv₁ deriv₂) (letval ih-e₁ ih-e₂) compat-proof = letval (ih-e₁ compat-proof) (ih-e₂ (⇑ᵣ-has-type compat-proof))
    case (letrecfn deriv₁ deriv₂) (letrecfn ih-e₁ ih-e₂) compat-proof = letrecfn (ih-e₁ (⇑ᵣ-has-type (⇑ᵣ-has-type compat-proof))) (ih-e₂ (⇑ᵣ-has-type compat-proof))

lookup-↑-commute : (sub : σ) → (x : 𝕏) → lookup (listMap ↑ sub) x ≡ maybeMap ↑ (lookup sub x)
lookup-↑-commute [] x = refl
lookup-↑-commute (x₁ ∷ s) zero = refl
lookup-↑-commute (x₁ ∷ s) (suc x) = lookup-↑-commute s x

lookup-var-⇑s : (sub : σ) → (x : 𝕏) → lookup-var (⇑ sub) (suc x) ≡ ↑ (lookup-var sub x)
lookup-var-⇑s [] x = refl
lookup-var-⇑s (x₁ ∷ s) zero = refl
lookup-var-⇑s (x₁ ∷ s) (suc x) rewrite lookup-↑-commute s x with lookup s x
lookup-var-⇑s (x₁ ∷ s) (suc x) | just x₂ = refl
lookup-var-⇑s (x₁ ∷ s) (suc x) | nothing = refl

⇑-has-type : ∀ {Γ Γ' s T} → Γ' ⊨σ s ∶ Γ → (Γ' , T) ⊨σ ⇑ s ∶ (Γ , T)
⇑-has-type {Γ} {Γ'} {s} {T} (compatible p) = compatible (λ {x} → compat-proof {x}) where
    compat-proof : ∀ {x T' Σ } → (Γ , T) x ≡ just T' → Σ ⨾ (Γ' , T) ⊢ lookup-var (⇑ s) (x) ∶ T'
    compat-proof {zero} {T'} {Σ} x-type = var x-type
    compat-proof {suc x} {T'} {Σ} x-type rewrite (lookup-var-⇑s s x) = RenamingLemma (p x-type) ↑-has-type

SubstitutionLemma : ∀ {Σ Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → (∀ {Γ' s} → Γ' ⊨σ s ∶ Γ → Σ ⨾ Γ' ⊢ subst s e ∶ T)
SubstitutionLemma {Σ} {_} {_} {_} derivation = ⊢-induction case derivation where
    P : TypeEnv → Expression → Type → Set
    P Γ e T = ∀ {Γ' s} → Γ' ⊨σ s ∶ Γ → Σ ⨾ Γ' ⊢ subst s e ∶ T
    case : ∀ {Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → IH P at Σ ⨾ Γ ⊢ e ∶ T → P Γ e T
    case int ih compat-proof = int
    case bool ih compat-proof = bool
    case (op+ _ _) (op+ ih-e₁ ih-e₂) compat-proof = (op+ (ih-e₁ compat-proof) (ih-e₂ compat-proof))
    case (op≥ _ _) (op≥ ih-e₁ ih-e₂) compat-proof = op≥ (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (if _ _ _) (if ih-e₁ ih-e₂ ih-e₃) compat-proof = if  (ih-e₁ compat-proof) (ih-e₂ compat-proof) (ih-e₃ compat-proof)
    case (assign _ _) (assign ℓ ih-e) compat-proof = assign ℓ (ih-e compat-proof)
    case (deref _) (deref ℓ) compat-proof = deref ℓ
    case skip ih compat-proof = skip
    case (seq _ _) (seq ih-e₁ ih-e₂) compat-proof = seq (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (while _ _) (while ih-e₁ ih-e₂) compat-proof = while (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (var x) ih (compatible s-x-well-typed) = s-x-well-typed x
    case (fn _) (fn ih-e) compat-proof = fn (ih-e (⇑-has-type compat-proof))
    case (app _ _)  (app ih-e₁ ih-e₂) compat-proof = app (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (letval deriv₁ deriv₂) (letval ih-e₁ ih-e₂) compat-proof = letval (ih-e₁ compat-proof) (ih-e₂ (⇑-has-type compat-proof))
    case (letrecfn deriv₁ deriv₂) (letrecfn ih-e₁ ih-e₂) compat-proof = letrecfn (ih-e₁ (⇑-has-type (⇑-has-type compat-proof))) (ih-e₂ (⇑-has-type compat-proof))