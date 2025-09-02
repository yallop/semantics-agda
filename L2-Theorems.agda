{-# OPTIONS --safe --without-K --exact-split #-}

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (false; true)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (just)
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬_; contraposition)
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
        (suc x) T → (Renaming (p x T) {{compatible (λ _ → refl)}})})

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
refAssignDiff {suc ℓ} {suc ℓ'} {n} [] ¬p = refAssignDiff {ℓ} {ℓ'} {n} [] (contraposition (cong suc) ¬p)
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
Progress : ∀ {Σ e T s} → Σ ⨾ • ⊢ e ∶ T → dom⊆ Σ s → val-or-step s e
Progress {Σ} {e} {s = s} derivation ∈s-if-∈Σ = structural-induction case e derivation where

  P : Expression → Set
  P e = ∀ {T} → Σ ⨾ • ⊢ e ∶ T → val-or-step s e

  case : ∀ {e} → IH P at e → P e
  case ih int = val value-N
  case ih bool = val value-B
  case (ihˡ [ + ] ihʳ) (op+ closedˡ closedʳ) with ihˡ closedˡ | ihʳ closedʳ
  ... | val value-N | val value-N = step op+
  ... | val value-N | step r = step (op2 value-N r)
  ... | step l | _ = step (op1 l)
  case (ihˡ [ ≥ ] ihʳ) (op≥ closedˡ closedʳ) with ihˡ closedˡ | ihʳ closedʳ
  ... | val value-N | val value-N = step op≥
  ... | val value-N | step r = step (op2 value-N r)
  ... | step l | _ = step (op1 l)
  case (If ih Then _ Else _) (if closed _ _) with ih closed
  ... | val (value-B {false}) = step if2
  ... | val (value-B {true}) = step if1
  ... | step r = step (if3 r)
  case (ℓ := ih) (assign ℓ∈Σ closed) with ih closed
  ... | val value-N with ⟨ _ , ℓ∈s ⟩ ← ∈s-if-∈Σ ℓ∈Σ = step (assign1 ℓ∈s)
  ... | step x = step (assign2 x)
  case ih (deref ℓ∈Σ) with ⟨ _ , ℓ∈s ⟩ ← ∈s-if-∈Σ ℓ∈Σ = step (deref ℓ∈s)
  case ih skip = val value-skip
  case (ih₁ ⨾ _) (seq closed₁ _) with ih₁ closed₁
  ... | val value-skip = step seq1
  ... | step r = step (seq2 r)
  case ih (while closed closed₁) = step while
  case ih (fn closed) = val value-Fn
  case (ihˡ ＠ ihʳ) (app closedˡ closedʳ) with ihˡ closedˡ | ihʳ closedʳ
  ... | val value-Fn | val value = step (fn value)
  ... | val value-Fn | step r = step (app2 value-Fn r)
  ... | step l | _ = step (app1 l)
  case (LetVal: T ≔ ih In _) (letval closed _) with ih closed
  ... | val value = step (let2 value)
  ... | step r = step (let1 r)
  case ih (letrecfn closed closed₁) = step letrecfn

≥2?↑-has-type : ∀ {Γ T T' T''} → (Γ ,,, T'' ,,, T' ,,, T) ⊢ρ ≥2?+1 ∶ (Γ ,,, T' ,,, T)
≥2?↑-has-type = compatible (λ {zero → refl ; (suc zero) → refl ; (suc (suc x)) → refl})

⇄-has-type : ∀ {Γ T T'} → (Γ ,,, T' ,,, T) ⊢ρ swap 0 ∶ (Γ ,,, T ,,, T')
⇄-has-type = compatible (λ {zero → refl ; (suc zero) → refl ; (suc (suc x)) → refl})

[e]ₛ-has-type : ∀ {Σ Γ T e} → Σ ⨾ Γ ⊢ e ∶ T → (Σ ⨟ Γ ⊨σ [ e ]ₛ ∶ (Γ ,,, T))
[e]ₛ-has-type deriv = compatible (λ {zero refl → deriv ; (suc _) Γn → var Γn})

-- Theorem 19 : Preservation
Preservation :  ∀ {Σ Γ T e s e' s'} →
   ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ → Σ ⨾ Γ ⊢ e ∶ T → dom⊆ Σ s → Σ ⨾ Γ ⊢ e' ∶ T × dom⊆ Σ s'
Preservation {Σ} {Γ} r = →-induction case r where

  P : Expression × Store → Expression × Store → Set
  P ⟨ e , s ⟩ ⟨ e' , s' ⟩ = ∀ {T} → Σ ⨾ Γ ⊢ e ∶ T → dom⊆ Σ s → Σ ⨾ Γ ⊢ e' ∶ T × dom⊆ Σ s'

  case : ∀ {s s' e e'} → IH P at ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ → P ⟨ e , s ⟩ ⟨ e' , s' ⟩
  case     op+              (op+ _ _)        d⊆ = ⟨ int , d⊆ ⟩
  case     op≥              (op≥ _ _)        d⊆ = ⟨ bool , d⊆ ⟩
  case     (op1 h₁)         (op+ e₁ e₂)      d⊆ with ⟨ e₁' , d⊆' ⟩ ← h₁ e₁ d⊆ = ⟨ op+ e₁' e₂ , d⊆' ⟩
  case     (op1 h₁)         (op≥ e₁ e₂)      d⊆ with ⟨ e₁' , d⊆' ⟩ ← h₁ e₁ d⊆ = ⟨ op≥ e₁' e₂ , d⊆' ⟩
  case     (op2 _ h₂)       (op+ e₁ e₂)      d⊆ with ⟨ e₂' , d⊆' ⟩ ← h₂ e₂ d⊆ = ⟨ op+ e₁ e₂' , d⊆' ⟩
  case     (op2 _ h₂)       (op≥ e₁ e₂)      d⊆ with ⟨ e₂' , d⊆' ⟩ ← h₂ e₂ d⊆ = ⟨ op≥ e₁ e₂' , d⊆' ⟩
  case     (deref _)        (deref _)        d⊆ = ⟨ int , d⊆ ⟩
  case {s} (assign1 _)      (assign _ _)     d⊆ = ⟨ skip , dom⊆-extend s d⊆ ⟩
  case     (assign2 h)      (assign ℓ e)     d⊆ with ⟨ e' , d⊆' ⟩ ← h e d⊆ = ⟨ assign ℓ e' , d⊆' ⟩
  case     seq1             (seq _ e)        d⊆ = ⟨ e , d⊆ ⟩
  case     (seq2 h₁)        (seq e₁ e₂)      d⊆ with ⟨ e₁' , d⊆' ⟩ ← h₁ e₁ d⊆ = ⟨ seq e₁' e₂ , d⊆' ⟩
  case     if1              (if _ e₂ _)      d⊆ = ⟨ e₂ , d⊆ ⟩
  case     if2              (if _ _ e₃)      d⊆ = ⟨ e₃ , d⊆ ⟩
  case     (if3 h₁)         (if e₁ e₂ e₃)    d⊆ with ⟨ e₁' , d⊆' ⟩ ← h₁ e₁ d⊆ = ⟨ if e₁' e₂ e₃ , d⊆' ⟩
  case     while            (while e₁ e₂)    d⊆ = ⟨ if e₁ (seq e₂ (while e₁ e₂)) skip , d⊆ ⟩
  case     (app1 h₁)        (app e₁ e₂)      d⊆ with ⟨ e₁' , d⊆' ⟩ ← h₁ e₁ d⊆ = ⟨ app e₁' e₂ , d⊆' ⟩
  case     (app2 _ h₂)      (app v₁ e₂)      d⊆ with ⟨ e₂' , d⊆' ⟩ ← h₂ e₂ d⊆ = ⟨ app v₁ e₂' , d⊆' ⟩
  case     (fn {e = e} _)   (app (fn v₁) v₂) d⊆ = ⟨ Substitution v₁ {{[e]ₛ-has-type v₂}} , d⊆ ⟩
  case     (let1 h₁)        (letval e₁ e₂)   d⊆ with ⟨ e₁' , d⊆' ⟩ ← h₁ e₁ d⊆ = ⟨ letval e₁' e₂ , d⊆' ⟩
  case     (let2 {e = e} _) (letval v₁ e₂)   d⊆ = ⟨ Substitution e₂ {{[e]ₛ-has-type v₁}} , d⊆ ⟩
  case      letrecfn        (letrecfn e₁ e₂) d⊆ = ⟨ Substitution e₂ {{[e]ₛ-has-type (fn (letrecfn (Renaming e₁ {{≥2?↑-has-type}}) (Renaming e₁ {{⇄-has-type}})))}} , d⊆ ⟩
