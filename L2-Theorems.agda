{-# OPTIONS --guardedness --safe --exact-split --copatterns #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (just; nothing) renaming (map to maybeMap)
open import Data.List using ([]; _∷_) renaming (map to listMap)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong) renaming (subst to ≡-subst)
open import Function.Base using (id)

open import L2
open import L2-Induction

data _⊨σ_∶_ : TypeEnv → σ → TypeEnv → Set where
    compatible : {Γ' : TypeEnv} → {s : σ} → {Γ : TypeEnv} → (∀ {T Σ} → (x : 𝕏) → Γ(x) ≡ just T → Σ ⨾ Γ' ⊢ lookup-var s x ∶ T) → Γ' ⊨σ s ∶ Γ

data _⊢ρ_∶_ : TypeEnv → ρ → TypeEnv → Set where
    compatible : {Γ' : TypeEnv} → {r : ρ} → {Γ : TypeEnv} → ((x : 𝕏) → Γ' (r x) ≡ Γ(x)) → Γ' ⊢ρ r ∶ Γ

↑-has-type : ∀ {Γ T} → (Γ , T) ⊢ρ suc ∶ Γ
↑-has-type = compatible (λ _ → refl)

⇑ᵣ-equiv : ∀ {Γ Γ' r T} → Γ' ⊢ρ r ∶ Γ → (x : 𝕏) → (Γ' , T) ((⇑ᵣ r) x) ≡ (Γ , T) x
⇑ᵣ-equiv _ zero = refl
⇑ᵣ-equiv (compatible p) (suc x) = p x

⇑ᵣ-has-type : ∀ {Γ Γ' T r} → Γ' ⊢ρ r ∶ Γ → (Γ' , T) ⊢ρ (⇑ᵣ r) ∶ (Γ , T)
⇑ᵣ-has-type p = compatible (⇑ᵣ-equiv p)

RenamingLemma : ∀ {Σ Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → ∀ {Γ' r} → Γ' ⊢ρ r ∶ Γ → Σ ⨾ Γ' ⊢ (rename r e) ∶ T
RenamingLemma {Σ} derivation =  ⊢-induction case derivation where
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
    case (var Γx∶T) ih (compatible p) = var (trans (p _) Γx∶T)
    case (fn deriv) (fn ih-e) compat-proof = fn (ih-e (⇑ᵣ-has-type compat-proof))
    case (app deriv₁ deriv₂) (app ih-e₁ ih-e₂) compat-proof = app (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (letval deriv₁ deriv₂) (letval ih-e₁ ih-e₂) compat-proof = letval (ih-e₁ compat-proof) (ih-e₂ (⇑ᵣ-has-type compat-proof))
    case (letrecfn deriv₁ deriv₂) (letrecfn ih-e₁ ih-e₂) compat-proof = letrecfn (ih-e₁ (⇑ᵣ-has-type (⇑ᵣ-has-type compat-proof))) (ih-e₂ (⇑ᵣ-has-type compat-proof))

lookup-↑-commute : (sub : σ) → (x : 𝕏) → lookup (listMap ↑ sub) x ≡ maybeMap ↑ (lookup sub x)
lookup-↑-commute [] _ = refl
lookup-↑-commute (_ ∷ s) zero = refl
lookup-↑-commute (_ ∷ s) (suc x) = lookup-↑-commute s x

lookup-var-⇑s : (sub : σ) → (x : 𝕏) → lookup-var (⇑ sub) (suc x) ≡ ↑ (lookup-var sub x)
lookup-var-⇑s [] _ = refl
lookup-var-⇑s (_ ∷ s) zero = refl
lookup-var-⇑s (_ ∷ s) (suc x) rewrite lookup-↑-commute s x with lookup s x
lookup-var-⇑s (_ ∷ s) (suc _) | just _ = refl
lookup-var-⇑s (_ ∷ s) (suc _) | nothing = refl

⇑-has-type : ∀ {Γ Γ' s T} → Γ' ⊨σ s ∶ Γ → (Γ' , T) ⊨σ ⇑ s ∶ (Γ , T)
⇑-has-type {Γ' = Γ'} {s} {T} (compatible p) = compatible (λ {
  zero x-type → var x-type ;
  {T = T'} {Σ} (suc x) x-type → ≡-subst (λ y → Σ ⨾ Γ' , T ⊢ y ∶ T') (sym (lookup-var-⇑s s x)) (RenamingLemma (p x x-type) ↑-has-type)})

SubstitutionLemma : ∀ {Σ Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → (∀ {Γ' s} → Γ' ⊨σ s ∶ Γ → Σ ⨾ Γ' ⊢ subst s e ∶ T)
SubstitutionLemma {Σ} derivation = ⊢-induction case derivation where
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
    case (var x) ih (compatible s-x-well-typed) = s-x-well-typed _ x
    case (fn _) (fn ih-e) compat-proof = fn (ih-e (⇑-has-type compat-proof))
    case (app _ _)  (app ih-e₁ ih-e₂) compat-proof = app (ih-e₁ compat-proof) (ih-e₂ compat-proof)
    case (letval deriv₁ deriv₂) (letval ih-e₁ ih-e₂) compat-proof = letval (ih-e₁ compat-proof) (ih-e₂ (⇑-has-type compat-proof))
    case (letrecfn deriv₁ deriv₂) (letrecfn ih-e₁ ih-e₂) compat-proof = letrecfn (ih-e₁ (⇑-has-type (⇑-has-type compat-proof))) (ih-e₂ (⇑-has-type compat-proof))
