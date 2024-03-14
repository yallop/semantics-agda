{-# OPTIONS --without-K --guardedness --safe --exact-split --copatterns #-}

open import Data.Nat hiding (_+_)
open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty
open import Data.List using (List; []; _∷_)
open import Data.Sum
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function.Base using (case_of_)

open import L1
open import L1-Induction

-- Lemma 9
values-don't-reduce :
  ∀ {v} → Value v →
  ∀ {s e' s'} → ¬ (⟨ v , s ⟩ ⟶ ⟨ e' , s' ⟩)
values-don't-reduce value-N ()
values-don't-reduce value-B ()
values-don't-reduce value-skip ()

-- Theorem 1: Determinacy
Determinacy :
  ∀ e {e₁ e₂ s s₁ s₂} →
  ⟨ e , s ⟩ ⟶ ⟨ e₁ , s₁ ⟩ →
  ⟨ e , s ⟩ ⟶ ⟨ e₂ , s₂ ⟩ →
  ⟨ e₁ , s₁ ⟩ ≡ ⟨ e₂ , s₂ ⟩
Determinacy = structural-induction case where

  ϕ : Expression → Set
  ϕ e = ∀ {e₁ e₂ s s₁ s₂} → ⟨ e , s ⟩ ⟶ ⟨ e₁ , s₁ ⟩ →
                           ⟨ e , s ⟩ ⟶ ⟨ e₂ , s₂ ⟩ →
                             ⟨ e₁ , s₁ ⟩ ≡ ⟨ e₂ , s₂ ⟩

  case : ∀ {e} → ϕ at e → ϕ e
  case (N _) ()
  case (B _) ()

  case (_ [ .+ ] _) op+ op+ = refl
  case (_ [ .≥ ] _) op≥ op≥  = refl
  case (_ [ _ ] ϕe) (op2 _ r₁) (op2 _ r₂) with refl ← ϕe r₁ r₂ = refl
  case (ϕe [ _ ] _) (op1 r₁) (op1 r₂) with refl ← ϕe r₁ r₂ = refl
  case (_ [ _ ] _) (op1 r) (op2 value-v _) = ⊥-elim (values-don't-reduce value-v r)
  case (_ [ _ ] _) (op2 value-v _) (op1 r) = ⊥-elim (values-don't-reduce value-v r)

  case (If _ Then _ Else _) if1 if1 = refl
  case (If _ Then _ Else _) if2 if2 = refl
  case (If ϕe Then _ Else _) (if3 r₁) (if3 r₂) with refl ← ϕe r₁ r₂ = refl
  
  case (_ := _) (assign1 _) (assign1 _) = refl
  case (_ := ϕe) (assign2 r₁) (assign2 r₂) with refl ← ϕe r₁ r₂ = refl
  
  case (! _) (deref lookup-ℓ) (deref lookup-ℓ') with refl ← (trans (sym lookup-ℓ) lookup-ℓ') = refl
  
  case Skip ()
  
  case (_ ؛ _) seq1 seq1 = refl
  case (ϕe ؛ _) (seq2 r₁) (seq2 r₂) with refl ← ϕe r₁ r₂ = refl
  
  case (While _ Do _) while while = refl


dom⊆ : TypeEnv → Store → Set
dom⊆ Γ s = ∀ {ℓ} → Γ ℓ ≡ just intref → ∃[ z ] ((s !! ℓ) ≡ just z)

refAssignSame : ∀ {n} s ℓ → (s ⨄ (ℓ ↦ n)) !! ℓ ≡ just n
refAssignSame    []    zero  = refl
refAssignSame (_ ∷ _)  zero  = refl
refAssignSame    []   (suc ℓ) = refAssignSame [] ℓ
refAssignSame (_ ∷ s) (suc ℓ) = refAssignSame s ℓ

refAssignDiff : ∀ {ℓ ℓ' n} → (s : Store) → ¬ (ℓ ≡ ℓ') → ((s ⨄ (ℓ ↦ n)) !! ℓ') ≡ s !! ℓ'
refAssignDiff {zero} {zero} s ¬p = ⊥-elim (¬p refl)
refAssignDiff {zero} {suc ℓ'} [] ¬p = refl
refAssignDiff {zero} {suc ℓ'} (x ∷ []) ¬p = refl
refAssignDiff {zero} {suc ℓ'} (x ∷ x₁ ∷ s) ¬p = refl
refAssignDiff {suc ℓ} {zero} [] ¬p = refl
refAssignDiff {suc ℓ} {zero} (x ∷ s) ¬p = refl
refAssignDiff {suc ℓ} {suc ℓ'} [] ¬p = refOutOfBounds ¬p
  where refOutOfBounds : ∀ {ℓ ℓ' n} → ¬ (ℓ ≡ ℓ') → ((ℓ ↦ n) !! ℓ') ≡ nothing
        refOutOfBounds {zero} {zero} ¬p = ⊥-elim (¬p refl)
        refOutOfBounds {zero} {suc ℓ'} ¬p = refl
        refOutOfBounds {suc ℓ} {zero} ¬p = refl
        refOutOfBounds {suc ℓ} {suc ℓ'} ¬p = refOutOfBounds (contraposition (cong suc) ¬p)
refAssignDiff {suc ℓ} {suc ℓ'} (x ∷ s) ¬p = refAssignDiff s (contraposition (cong suc) ¬p)

dom⊆-extend : ∀ {s ℓ Γ n} → dom⊆ Γ s → dom⊆ Γ (s ⨄ (ℓ ↦ n))
dom⊆-extend {[]} {ℓ} d⊆ {ℓ'} eq with ⟨ _ , () ⟩ ← d⊆ eq
dom⊆-extend {x ∷ s} {ℓ} d⊆ {ℓ'} eq with ℓ ≟ ℓ' | d⊆ eq
... | yes refl | _  = ⟨ _ , refAssignSame (x ∷ s) ℓ ⟩
dom⊆-extend {s} d⊆ _ | no ¬p | ⟨ fst , eq' ⟩ = ⟨ fst , trans (refAssignDiff s ¬p) eq' ⟩


-- Theorem 2: Progress

data val-or-step (s : Store) (e : Expression) : Set where
  val : Value e →  val-or-step s e
  step : ∀ {e' s'} → ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ → val-or-step s e

Progress : ∀ {Γ e T s} → Γ ⊢ e ∶ T → dom⊆ Γ s → val-or-step s e
Progress {Γ} {_} {_} {s} derivation ∈s-if-∈Γ = ⊢-induction case derivation where
  P : Expression → Type → Set
  P e τ = val-or-step s e
  case : ∀ {e τ} → Γ ⊢ e ∶ τ → P at Γ ⊢ e ∶ τ → P e τ
  case  _            int                              = val value-N
  case  _            bool                             = val value-B
  case (op+ _ _)    (op+ (val value-N) (val value-N)) = step op+
  case (op+ _ _)    (op+ (val value-N) (step r))      = step (op2 value-N r)
  case (op+ _ _)    (op+ (step r) _)                  = step (op1 r)
  case (op≥ _ _)    (op≥ (val value-N) (val value-N)) = step op≥
  case (op≥ _ _)    (op≥ (val value-N) (step r))      = step (op2 value-N r)
  case (op≥ _ _)    (op≥ (step r) _)                  = step (op1 r)
  case (if _ _ _)   (if (val (value-B {true})) _ _)   = step if1
  case (if _ _ _)   (if (val (value-B {false})) _ _)  = step if2
  case (if _ _ _)   (if (step r) _ _)                 = step (if3 r)
  case (assign _ _) (assign ℓ∈Γ (val value-N))        = let ⟨ _ , ℓ∈s ⟩ = ∈s-if-∈Γ ℓ∈Γ in step (assign1 ℓ∈s)
  case (assign _ _) (assign _ (step r))               = step (assign2 r)
  case (deref _)    (deref ℓ∈Γ)                       = let ⟨ _ , ℓ∈s ⟩ = ∈s-if-∈Γ ℓ∈Γ in step (deref ℓ∈s)
  case  _            skip                             = val value-skip
  case (seq _ _)    (seq (val value-skip) _)          = step seq1
  case (seq _ _)    (seq (step y) _)                  = step (seq2 y)
  case (while _ _)  (while _ _)                       = step while


-- Theorem 3: Preservation
Preservation :  ∀ {Γ T e s e' s'} →
   ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ → Γ ⊢ e ∶ T → dom⊆ Γ s → Γ ⊢ e' ∶ T × dom⊆ Γ s'
Preservation {Γ} r = →-induction case r where
  P : Expression × Store → Expression × Store → Set
  P ⟨ e , s ⟩ ⟨ e' , s' ⟩ = ∀ {T} → Γ ⊢ e ∶ T → dom⊆ Γ s → Γ ⊢ e' ∶ T × dom⊆ Γ s'
  case : ∀ {s s' e e'} → P at ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ → P ⟨ e , s ⟩ ⟨ e' , s' ⟩
  case     op+         (op+ _ _) d⊆    = ⟨ int , d⊆ ⟩
  case     op≥         (op≥ _ _) d⊆    = ⟨ bool , d⊆ ⟩
  case     (op1 p)     (op+ e e₁) d⊆   = let ⟨ e₂ , d⊆' ⟩ = p e d⊆ in ⟨ op+ e₂ e₁ , d⊆' ⟩
  case     (op1 p)     (op≥ e e₁) d⊆   = let ⟨ e₂ , d⊆' ⟩ = p e d⊆ in ⟨ op≥ e₂ e₁ , d⊆' ⟩
  case     (op2 _ p)   (op+ e e₁) d⊆   = let ⟨ e₂ , d⊆' ⟩ = p e₁ d⊆ in ⟨ op+ e e₂ , d⊆' ⟩
  case     (op2 _ p)   (op≥ e e₁) d⊆   = let ⟨ e₂ , d⊆' ⟩ = p e₁ d⊆ in ⟨ op≥ e e₂ , d⊆' ⟩
  case     (deref _)   (deref _) d⊆    = ⟨ int , d⊆ ⟩
  case {s} (assign1 _) (assign _ _) d⊆ = ⟨ skip , dom⊆-extend {s} d⊆ ⟩
  case     (assign2 p) (assign ℓ e) d⊆ = let ⟨ e₁ , d⊆' ⟩ = p e d⊆ in ⟨ assign ℓ e₁ , d⊆' ⟩
  case     seq1        (seq _ e) d⊆    = ⟨ e , d⊆ ⟩
  case     (seq2 p)    (seq e e₁) d⊆   = let ⟨ e₂ , d⊆' ⟩  = p e d⊆  in ⟨ seq e₂ e₁ , d⊆' ⟩
  case     if1         (if _ e₁ _) d⊆  = ⟨ e₁ , d⊆ ⟩
  case     if2         (if _ _ e₂) d⊆  = ⟨ e₂ , d⊆ ⟩
  case     (if3 p)     (if e e₁ e₂) d⊆ = let ⟨ e₃ , d⊆' ⟩ = p e d⊆ in ⟨ if e₃ e₁ e₂ , d⊆' ⟩
  case     while       (while e e₁) d⊆ = ⟨ if e (seq e₁ (while e e₁)) skip , d⊆ ⟩


-- Theorem 4: Safety
Safety :
  ∀ {Γ e T s e' s'} →
   Γ ⊢ e ∶ T →
   dom⊆ Γ s →
  ⟨ e , s ⟩ ⟶⋆ ⟨ e' , s' ⟩ →
  val-or-step s' e'
-- Proof. Follows from progress and preservation
--        by induction on the reduction sequence
Safety t d · = Progress t d
Safety t d (r then rs) with ⟨ t' , d' ⟩ ← Preservation r t d = Safety t' d' rs

-- Theorem 7 (Uniqueness of typing)
unique : ∀ {Γ e T T'} → Γ ⊢ e ∶ T → Γ ⊢ e ∶ T' → T ≡ T'
-- Proof. By mutual induction on the two typing derivations
unique int int = refl
unique bool         bool         = refl
unique (op+ _ _)    (op+ _ _)    = refl
unique (op≥ _ _)    (op≥ _ _)    = refl
unique (if _ _ t)   (if _ _ t')  = unique t t'
unique (assign _ _) (assign _ _) = refl
unique (deref _)    (deref _)    = refl
unique skip         skip         = refl
unique (seq _ t)    (seq _ t')   = unique t t'
unique (while _ _)  (while _ _)  = refl

-- Theorem 5 (Decidability-of-typeability)
_⊢_∶? : ∀ Γ e → Dec (∃[ T ] Γ ⊢ e ∶ T)
Γ ⊢ N x ∶? = yes ⟨ int , int ⟩
Γ ⊢ B x ∶?  = yes ⟨ bool , bool ⟩
Γ ⊢ e₁ [ + ] e₂ ∶? with Γ ⊢ e₁ ∶?  | Γ ⊢ e₂ ∶?
… | yes ⟨ T₁ , t₁ ⟩ | yes ⟨ T₂ , t₂ ⟩ with ≡-type T₁ int | ≡-type T₂ int
… | yes refl | yes refl = yes ⟨ _ , op+ t₁ t₂ ⟩
… | no ¬eq | _ = no λ { ⟨ _ , op+ t₁' _ ⟩ → ¬eq (unique t₁ t₁') }
… | yes refl | no ¬eq = no λ { ⟨ _ , op+ _ t₂' ⟩ → ¬eq (unique t₂ t₂') }
Γ ⊢ e₁ [ + ] e₂ ∶? | no ¬t₁ | _ = no λ { ⟨ _ , op+ t₁' _ ⟩ → ¬t₁ ⟨ _ , t₁' ⟩ }
Γ ⊢ e₁ [ + ] e₂ ∶? | yes _ | no ¬t₂ = no λ { ⟨ _ , op+ _ t₂' ⟩ → ¬t₂ ⟨ _ , t₂' ⟩ }
Γ ⊢ e₁ [ ≥ ] e₂ ∶? with Γ ⊢ e₁ ∶?  | Γ ⊢ e₂ ∶?
… | yes ⟨ T₁ , t₁ ⟩ | yes ⟨ T₂ , t₂ ⟩ with ≡-type T₁ int | ≡-type T₂ int
… | yes refl | yes refl = yes ⟨ _ , op≥ t₁ t₂ ⟩
… | no ¬eq | _ = no λ { ⟨ _ , op≥ t₁' _ ⟩ → ¬eq (unique t₁ t₁') }
… | yes refl | no ¬eq = no λ { ⟨ _ , op≥ _ t₂' ⟩ → ¬eq (unique t₂ t₂') }
Γ ⊢ e₁ [ ≥ ] e₂ ∶? | no ¬t₁          | _ = no λ { ⟨ _ , op≥ t₁' _ ⟩ → ¬t₁ ⟨ _ , t₁' ⟩ }
Γ ⊢ e₁ [ ≥ ] e₂ ∶?  | yes _          | no ¬t₂ = no λ { ⟨ _ , op≥ _ t₂' ⟩ → ¬t₂ ⟨ _ , t₂' ⟩ }
Γ ⊢ If e₁ Then e₂ Else e₃ ∶? with Γ ⊢ e₁ ∶?  | Γ ⊢ e₂ ∶? | Γ ⊢ e₃ ∶?
… | yes ⟨ T₁ , t₁ ⟩ | yes ⟨ T₂ , t₂ ⟩ | yes ⟨ T₃ , t₃ ⟩ with ≡-type T₁ bool | ≡-type T₂ T₃
… | yes refl | yes refl = yes ⟨ T₂ , if t₁ t₂ t₃ ⟩
… | no neq   | _ = no λ { ⟨ fst , if t₁' _ _ ⟩ → neq (unique t₁ t₁') }
… | yes refl | no neq = no refute
  where refute : ∃[ T ] Γ ⊢ If e₁ Then e₂ Else e₃ ∶ T → ⊥
        refute ⟨ fst , if snd snd₁ snd₂ ⟩ rewrite unique t₃ snd₂ rewrite unique t₂ snd₁ = neq refl
Γ ⊢ If e₁ Then e₂ Else e₃ ∶? | no ¬t₁ | _ | _ = no λ { ⟨ _ , if t₁' _ _ ⟩ → ¬t₁ ⟨ _ , t₁' ⟩ }
Γ ⊢ If e₁ Then e₂ Else e₃ ∶? | yes _ | no ¬t₂ | _ = no λ { ⟨ _ , if _ t₂' _ ⟩ → ¬t₂ ⟨ _ , t₂' ⟩ }
Γ ⊢ If e₁ Then e₂ Else e₃ ∶? | yes _ | yes _ | no ¬t₃ = no λ { ⟨ _ , if _ _ t₃' ⟩ → ¬t₃ ⟨ _ , t₃' ⟩ }
Γ ⊢ ℓ := e ∶? with Γ ⊢ e ∶?
Γ ⊢ ℓ := e ∶? | no ¬t = no λ { ⟨ _ , assign _ t ⟩ → ¬t ⟨ _ , t ⟩ }
Γ ⊢ ℓ := e ∶? | yes ⟨ T , _ ⟩ with ≡-type T int | Γ(ℓ) in eq
Γ ⊢ ℓ := e ∶? | yes ⟨ _ , t ⟩ | yes refl | just intref = yes ⟨ _ , assign eq t ⟩
Γ ⊢ ℓ := e ∶? | yes ⟨ _ , t ⟩ | yes refl | nothing = no λ { ⟨ _ , assign eq' _ ⟩ → case trans (sym eq) eq' of λ ()  }
Γ ⊢ ℓ := e ∶? | yes ⟨ _   , t ⟩ | no ¬p | _ = no (λ { ⟨ _ , assign _ t' ⟩ → ¬p (unique t t') })


Γ ⊢ ! ℓ ∶?  with Γ(ℓ) in eq
… | just intref = yes ⟨ int , deref eq ⟩
… | nothing = no λ { ⟨ _ , deref x ⟩ → case trans (sym eq) x of λ () }
Γ ⊢ Skip ∶? = yes ⟨ unit , skip ⟩
Γ ⊢ e₁ ؛ e₂ ∶?  with Γ ⊢ e₁ ∶?  | Γ ⊢ e₂ ∶?
… | yes ⟨ T₁ , t₁ ⟩ | yes ⟨ T , t₂ ⟩ = typecase (≡-type T₁ unit)
  where typecase : Dec (T₁ ≡ unit) → Dec (∃[ T ] Γ ⊢ e₁ ؛ e₂ ∶ T)
        typecase (yes refl) = yes ⟨ T , seq t₁ t₂ ⟩
        typecase (no neq  ) = no λ { ⟨ fst , seq t₁' _ ⟩ → neq (unique t₁ t₁') }

… | no ¬t₁ | _ = no λ { ⟨ _ , seq t₁' _ ⟩ → ¬t₁ ⟨ _ , t₁' ⟩ }
… | yes _ | no ¬t₂ = no λ { ⟨ _ , seq _ t₂' ⟩ → ¬t₂ ⟨ _ , t₂' ⟩ }
Γ ⊢ While e₁ Do e₂ ∶? with Γ ⊢ e₁ ∶? | Γ ⊢ e₂ ∶?
Γ ⊢ While e₁ Do e₂ ∶? | yes ⟨ T₁ , _ ⟩ | yes ⟨ T₂ , _ ⟩ with ≡-type T₁ bool | ≡-type T₂ unit
Γ ⊢ While e₁ Do e₂ ∶? | yes ⟨ .bool , t₁ ⟩ | yes ⟨ .unit , t₂ ⟩ | yes refl | yes refl = yes ⟨ _ , (while t₁ t₂) ⟩
Γ ⊢ While e₁ Do e₂ ∶? | yes ⟨ _ , t₁ ⟩ | _ | no ¬p | _ = no λ { ⟨ .unit , while t₁' _ ⟩ → ¬p (unique t₁ t₁') }
Γ ⊢ While e₁ Do e₂ ∶? | _ | yes ⟨ _ , t₂ ⟩ | yes refl | no ¬p = no λ { ⟨ .unit , while _ t₂' ⟩ → ¬p (unique t₂ t₂') }

Γ ⊢ While e₁ Do e₂ ∶? | no ¬t₁ | _ = no λ { ⟨ _ , while t₁' _ ⟩ → ¬t₁ ⟨ _ , t₁' ⟩ }
Γ ⊢ While e₁ Do e₂ ∶? | yes _ | no ¬t₂ = no λ { ⟨ _ , while _ t₂' ⟩ → ¬t₂ ⟨ _ , t₂' ⟩ }

-- Theorem 6: Decidability of type checking
_⊢_∶_?? : ∀ Γ e T → Dec (Γ ⊢ e ∶ T)
-- Proof. Follows from decidablity of typeability ...
Γ ⊢ e ∶ T ?? with Γ ⊢ e ∶?
Γ ⊢ e ∶ T ?? | no ¬p = no λ p → ¬p ⟨ _ , p ⟩
Γ ⊢ e ∶ T ?? | yes ⟨ T' , _ ⟩ with ≡-type T T'
Γ ⊢ e ∶ T ?? | yes ⟨ _  , t ⟩ | yes refl = yes t
--                                      ... and uniqueness of typing
Γ ⊢ e ∶ T ?? | yes ⟨ _  , t ⟩ | no ¬eq = no (λ { r → ¬eq (unique r t) })
