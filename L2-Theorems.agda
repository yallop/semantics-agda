{-# OPTIONS --safe --without-K --exact-split #-}

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (false; true)
open import Data.Product using (∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (just)
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; trans)

open import L2
open import L2-Induction

data _⊢ρ_∶_ (Γ' : TypeEnv) (r : ρ)  (Γ : TypeEnv)  : Set where
    compatible : (∀ x  → Γ' (r x) ≡ Γ(x)) → Γ' ⊢ρ r ∶ Γ

⇑ᵣ-equiv : ∀ {Γ Γ' r T} → Γ' ⊢ρ r ∶ Γ → (x : 𝕏) → (Γ' ,,, T) ((⇑ᵣ r) x) ≡ (Γ ,,, T) x
⇑ᵣ-equiv _ zero = refl
⇑ᵣ-equiv (compatible p) (suc x) = p x

instance
    ⇑ᵣ-has-type : ∀ {Γ Γ' T r} → {{Γ' ⊢ρ r ∶ Γ}} → (Γ' ,,, T) ⊢ρ (⇑ᵣ r) ∶ (Γ ,,, T)
    ⇑ᵣ-has-type {{p}} = compatible (⇑ᵣ-equiv p)

Renaming : ∀ {Σ Γ e T Γ' r} → Σ ⨾ Γ ⊢ e ∶ T → {{Γ' ⊢ρ r ∶ Γ}} → Σ ⨾ Γ' ⊢ rename r e ∶ T
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
    case (fn h)                            = fn h
    case (app h₁ h₂)                       = app h₁ h₂
    case (letval h₁ h₂)                    = letval h₁ h₂
    case (letrecfn h₁ h₂)                  = letrecfn h₁ h₂

data _⨟_⊨σ_∶_ (Σ : StoreEnv) (Γ' : TypeEnv) (s : σ)  (Γ : TypeEnv) : Set where
    compatible : (∀ {T} x → Γ(x) ≡ just T → Σ ⨾ Γ' ⊢ s x ∶ T) → Σ ⨟ Γ' ⊨σ s ∶ Γ

instance
    ⇑-has-type : ∀ {Σ Γ Γ' s T} → {{Σ ⨟ Γ' ⊨σ s ∶ Γ}} → (Σ ⨟ (Γ' ,,, T) ⊨σ ⇑ s ∶ (Γ ,,, T))
    ⇑-has-type {{compatible p}} = compatible (λ {
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
    case (fn h)                            = fn h
    case (app h₁ h₂)                       = app h₁ h₂
    case (letval h₁ h₂)                    = letval h₁ h₂
    case (letrecfn h₁ h₂)                  = letrecfn h₁ h₂



dom⊆ : StoreEnv → Store → Set
dom⊆ Σ s = ∀ {ℓ} → Σ ℓ ≡ just intref → ∃[ z ] ((s !! ℓ) ≡ just z)

refAssignSame : ∀ {n} s ℓ → (s ⨄ (ℓ ↦ n)) !! ℓ ≡ just n
refAssignSame    []    zero  = refl
refAssignSame (_ ∷ _)  zero  = refl
refAssignSame    []   (suc ℓ) = refAssignSame [] ℓ
refAssignSame (_ ∷ s) (suc ℓ) = refAssignSame s ℓ

refAssignDiff : ∀ {ℓ ℓ' n} → (s : Store) → ¬ (ℓ ≡ ℓ') → ((s ⨄ (ℓ ↦ n)) !! ℓ') ≡ s !! ℓ'
refAssignDiff {zero} {zero} s ¬p = ⊥-elim (¬p refl)
refAssignDiff {zero} {suc ℓ'} [] _ = refl
refAssignDiff {zero} {suc ℓ'} (_ ∷ []) _ = refl
refAssignDiff {zero} {suc ℓ'} (_ ∷ _ ∷ _) _ = refl
refAssignDiff {suc ℓ} {zero} [] _ = refl
refAssignDiff {suc ℓ} {zero} (_ ∷ _) _ = refl
refAssignDiff {suc ℓ} {suc ℓ'} [] ¬p = refAssignDiff [] (contraposition (cong suc) ¬p)
refAssignDiff {suc ℓ} {suc ℓ'} (_ ∷ s) ¬p = refAssignDiff s (contraposition (cong suc) ¬p)

dom⊆-extend : ∀ {ℓ Σ n} s → dom⊆ Σ s → dom⊆ Σ (s ⨄ (ℓ ↦ n))
dom⊆-extend [] d⊆ eq with ⟨ _ , () ⟩ ← d⊆ eq
dom⊆-extend {ℓ} (x ∷ s) d⊆ {ℓ'} eq with ℓ ≟ ℓ' | d⊆ eq
... | yes refl | _  = ⟨ _ , refAssignSame (x ∷ s) ℓ ⟩
dom⊆-extend s d⊆ _ | no ¬p | ⟨ fst , eq' ⟩ = ⟨ fst , trans (refAssignDiff s ¬p) eq' ⟩

data val-or-step (s : Store) (e : Expression) : Set where
  val : Value e →  val-or-step s e
  step : ∀ {e' s'} → ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ → val-or-step s e

-- Theorem 18: Progress
Progress : ∀ {Σ Γ e T s} → Σ ⨾ Γ ⊢ e ∶ T → dom⊆ Σ s → Γ ≡ • → val-or-step s e
Progress {Σ} {s = s} derivation ∈s-if-∈Σ = ⊢-induction case derivation where

  P : TypeEnv → Expression → Type → Set
  P Γ e T = Γ ≡ • → val-or-step s e

  case : ∀ {Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → IH P at Σ ⨾ Γ ⊢ e ∶ T → P Γ e T
  case int            ih                     e-closed = val value-N
  case bool           ih                     e-closed = val value-B
  case (op+ _ _)      (op+ h₁ h₂)            e-closed with h₁ e-closed | h₂ e-closed
  ... | val value-N | val value-N                     = step op+
  ... | val value-N | step r                          = step (op2 value-N r)
  ... | step r      | _                               = step (op1 r)
  case (op≥ _ _)      (op≥ h₁ h₂)            e-closed with h₁ e-closed | h₂ e-closed
  ... | val value-N | val value-N                     = step op≥
  ... | val value-N | step r                          = step (op2 value-N r)
  ... | step r      | _                               = step (op1 r)
  case (if _ _ _)     (if h₁ _ _)            e-closed with h₁ e-closed
  ... | val (value-B {true})                          = step if1
  ... | val (value-B {false})                         = step if2
  ... | step r                                        = step (if3 r)
  case (assign _ _)   (assign ℓ∈Σ h)         e-closed with h e-closed
  ... | val value-N   with ⟨ _ , ℓ∈s ⟩ ← ∈s-if-∈Σ ℓ∈Σ = step (assign1 ℓ∈s)
  ... | step r                                        = step (assign2 r)
  case (deref _)      (deref ℓ∈Σ)            e-closed with ⟨ _ , ℓ∈s ⟩ ← ∈s-if-∈Σ ℓ∈Σ = step (deref ℓ∈s)
  case skip           _                      e-closed = val value-skip
  case (seq _ _)      (seq h₁ _)             e-closed with h₁ e-closed
  ... | val value-skip                                = step seq1
  ... | step r                                        = step (seq2 r)
  case (while _ _)    _                      e-closed = step while
  case (var ())       _                      refl
  case (fn _)         _                      e-closed = val value-Fn
  case (app _ _)      (app h₁ h₂)            e-closed with h₁ e-closed | h₂ e-closed
  ... | val value-Fn | val value                      = step (fn value)
  ... | val value-Fn | step r                         = step (app2 value-Fn r)
  ... | step r       | _                              = step (app1 r)
  case (letval _ _)   (letval h₁ _)          e-closed with h₁ e-closed
  ... | val value                                     = step (let2 value)
  ... | step r                                        = step (let1 r)
  case (letrecfn _ _) (letrecfn h₁ h₂)       e-closed = step (letrecfn)
