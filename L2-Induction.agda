{-# OPTIONS --without-K --safe --exact-split #-}

open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (just)
open import Data.Integer using (ℤ; 0ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

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
    P (Γ ,,, T₁) e T₂ →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ (Fn: T₁ ⇒ e) ∶ (T₁ ➝ T₂)

  app : ∀ { Σ Γ T₁ T₂ e₁ e₂ } →
    P Γ e₁ (T₁ ➝ T₂) →
    P Γ e₂ T₁ →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ e₁ ＠ e₂ ∶ T₂

  letval : ∀ { Σ Γ T₁ T₂ e₁ e₂ } →
    P Γ e₁ T₁ →
    P (Γ ,,, T₁) e₂ T₂ →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ LetVal: T₁ ≔ e₁ In e₂ ∶ T₂

  letrecfn : ∀ { Σ Γ T₁ T₂ T e₁ e₂ } →
    P (Γ ,,, ( T₁ ➝ T₂ ) ,,, T₁) e₁ T₂ →
    P ( Γ ,,, ( T₁ ➝ T₂ ) ) e₂ T →
    ------------------------
    IH P at Σ ⨾ Γ ⊢ LetValRec: T₁ ➝ T₂ ≔[Fn: T₁ ⇒ e₁ ]In e₂ ∶ T

⊢-induction : ∀ {Σ Γ e T} →
    ∀ {P : TypeEnv → Expression → Type → Set} →
    (∀ {Γ e T} → Σ ⨾ Γ ⊢ e ∶ T → IH P at Σ ⨾ Γ ⊢ e ∶ T → P Γ e T) →
    (Σ ⨾ Γ ⊢ e ∶ T) →
    P Γ e T
⊢-induction k te@int = k te int      -- te stands for typed expression, is an alias for the whole expression
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

⊢-induction-simple : ∀ {Σ Γ e T} →
    ∀ {P : TypeEnv → Expression → Type → Set} →
    (∀ {Γ e T} → IH P at Σ ⨾ Γ ⊢ e ∶ T → P Γ e T) →
    Σ ⨾ Γ ⊢ e ∶ T →
    P Γ e T
⊢-induction-simple k deriv = ⊢-induction (λ _ → k) deriv

data IH_at_⟶_ (P : Expression × Store → Expression × Store → Set)
                   : Expression × Store → Expression × Store → Set where

  op+ : ∀ {n₁ n₂ s} →
        IH P at ⟨ N n₁ [ + ] N n₂ , s ⟩ ⟶ ⟨ N (n₁ +ℤ n₂) , s ⟩

  op≥ : ∀ {n₁ n₂ s} →
        IH P at ⟨ N n₁ [ ≥ ] N n₂ , s ⟩ ⟶ ⟨ B (n₂ ≤ℤ n₁) , s ⟩

  op1 : ∀ {e₁ op e₂ s e₁' s'} →
       P ⟨ e₁ , s ⟩ ⟨ e₁' , s' ⟩  →
       ------------------------------------------
       IH P at ⟨ e₁ [ op ] e₂ , s ⟩ ⟶ ⟨ e₁' [ op ] e₂ , s' ⟩

  op2 : ∀ {v e₂ s e₂' s' op} →
       Value v →
       P ⟨ e₂ , s ⟩ ⟨ e₂' , s' ⟩  →
       ------------------------------------------
       IH P at ⟨ v [ op ] e₂ , s ⟩ ⟶ ⟨ v [ op ] e₂' , s' ⟩

  deref : ∀ {ℓ n s} →
       (s !! ℓ ≡ just n) →
       IH P at ⟨ ! ℓ , s ⟩ ⟶ ⟨ N n , s ⟩

  assign1 : ∀ {ℓ m n s} →
       s !! ℓ ≡ just m →
       IH P at ⟨ ℓ := N n , s ⟩ ⟶ ⟨ Skip , s ⨄ (ℓ ↦ n) ⟩

  assign2 : ∀ {ℓ e s e' s'} →
       P ⟨ e , s ⟩ ⟨ e' , s' ⟩ →
      --------------------------------
       IH P at ⟨ ℓ := e , s ⟩ ⟶ ⟨ ℓ := e' , s' ⟩

  seq1 : ∀ {e₂ s} →
       IH P at ⟨ Skip ⨾ e₂ , s ⟩ ⟶ ⟨ e₂ , s ⟩

  seq2 : ∀ {e₁ e₂ s e₁' s'} →
       P ⟨ e₁ , s ⟩ ⟨ e₁' , s' ⟩ →
      --------------------------------
       IH P at ⟨ e₁ ⨾ e₂ , s ⟩ ⟶ ⟨ e₁' ⨾ e₂ , s' ⟩

  if1 : ∀ {e₂ e₃ s} →
      IH P at ⟨ If B true Then e₂ Else e₃ , s ⟩ ⟶ ⟨ e₂ , s ⟩

  if2 : ∀ {e₂ e₃ s} →
      IH P at ⟨ If B false Then e₂ Else e₃ , s ⟩ ⟶ ⟨ e₃ , s ⟩

  if3 : ∀ {e₁ e₂ e₃ s e₁' s'} →
      P ⟨ e₁ , s ⟩ ⟨ e₁' , s' ⟩ →
      -----------------------------------------------------------
      IH P at ⟨ If e₁ Then e₂ Else e₃ , s ⟩ ⟶ ⟨ If e₁' Then e₂ Else e₃ , s' ⟩

  while : ∀ {e₁ e₂ s} →
      IH P at ⟨ While e₁ Do e₂ , s ⟩ ⟶ ⟨ If e₁ Then (e₂ ⨾ (While e₁ Do e₂)) Else Skip , s ⟩

  app1 : ∀ { e₁ e₂ e₁' s s' } →
      P ⟨ e₁ , s ⟩ ⟨ e₁' , s' ⟩ →
      ----------------------------------
      IH P at ⟨ e₁ ＠ e₂ , s ⟩ ⟶ ⟨ e₁' ＠ e₂ , s' ⟩

  app2 : ∀ { v e₂ e₂' s s' } →
      Value v →
      P ⟨ e₂ , s ⟩ ⟨ e₂' , s' ⟩ →
      ----------------------------------
      IH P at ⟨ v ＠ e₂ , s ⟩ ⟶ ⟨ v ＠ e₂' , s' ⟩

  fn : ∀ { v e s T } →
      Value v →
      ----------------------------------
      IH P at ⟨ (Fn: T ⇒ e) ＠ v , s ⟩ ⟶ ⟨ subst [ v ]ₛ e , s ⟩

  let1 :  ∀ { e₁ e₂ e₁' s s' T } →
    P ⟨ e₁ , s ⟩ ⟨ e₁' , s' ⟩ →
    -------------------------------
    IH P at ⟨ LetVal: T ≔ e₁ In e₂ , s ⟩ ⟶ ⟨ LetVal: T ≔ e₁' In e₂ , s' ⟩

  let2 :  ∀ { v e s T } →
    Value v →
    -------------------------------
    IH P at ⟨ LetVal: T ≔ v In e , s ⟩ ⟶ ⟨ subst [ v ]ₛ e , s ⟩

  letrecfn : ∀ { e₁ e₂ s T₁ T₂ } →
    IH P at ⟨ LetValRec: T₁ ➝ T₂ ≔[Fn: T₁ ⇒ e₁ ]In e₂ , s ⟩ ⟶
    ⟨ subst ([ (Fn: T₁ ⇒ LetValRec: T₁ ➝ T₂  ≔[Fn: T₁ ⇒ ≥2?↑ e₁ ]In (⇄ e₁)) ]ₛ) e₂ , s ⟩

→-induction :
  ∀ {e s e' s'} →
  {P : Expression × Store → Expression × Store → Set} →
  (∀ {e s e' s'} → IH P at ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ → P ⟨ e , s ⟩ ⟨ e' , s' ⟩) →
  ⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩ →  P ⟨ e , s ⟩ ⟨ e' , s' ⟩
→-induction k op+ = k op+
→-induction k op≥ = k op≥
→-induction k (op1 step) = k (op1 (→-induction k step))
→-induction k (op2 isVal step) = k (op2 isVal (→-induction k step))
→-induction k (deref locInStore) = k (deref locInStore)
→-induction k (assign1 locInStore) = k (assign1 locInStore)
→-induction k (assign2 step) = k (assign2 (→-induction k step))
→-induction k seq1 = k seq1
→-induction k (seq2 step) = k (seq2 (→-induction k step))
→-induction k if1 = k if1
→-induction k if2 = k if2
→-induction k (if3 step) = k (if3 (→-induction k step))
→-induction k while = k while
→-induction k (app1 step) = k (app1 (→-induction k step))
→-induction k (app2 isVal step) = k (app2 isVal (→-induction k step))
→-induction k (fn isVal) = k (fn isVal)
→-induction k (let1 step) = k (let1 (→-induction k step))
→-induction k (let2 isVal) = k (let2 isVal)
→-induction k letrecfn = k letrecfn
