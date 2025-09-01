{-# OPTIONS --without-K --guardedness --safe --exact-split #-}

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_)
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; -1ℤ; +_) renaming (_+_ to _+ℤ_; _≤ᵇ_ to _≤ℤ_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import L2

slide-129-expression : Expression
slide-129-expression = (Fn: int ⇒ (Fn: int ⇒ (Var 1) [ + ] (Var 0))) ＠ (N (+_ 3) [ + ] N (+_ 4)) ＠ (N (+_ 5))

slide-129-reduction-1 : ∀ {s} → ⟨ (Fn: int ⇒ (Fn: int ⇒ (Var 1) [ + ] (Var 0))) ＠ (N (+_ 3) [ + ] N (+_ 4)) ＠ (N (+_ 5)) , s ⟩ ⟶ ⟨ (Fn: int ⇒ (Fn: int ⇒ (Var 1) [ + ] (Var 0))) ＠ (N (+_ 7)) ＠ (N (+_ 5)) , s ⟩
slide-129-reduction-1 = app1 (app2 value-Fn op+)

slide-129-reduction-2 : ∀ { s } → ⟨ (Fn: int ⇒ (Fn: int ⇒ (Var 1) [ + ] (Var 0))) ＠ (N (+_ 7)) ＠ (N (+_ 5)) , s ⟩ ⟶ ⟨ (Fn: int ⇒ (N (+_ 7)) [ + ] (Var 0)) ＠ (N (+_ 5)) , s ⟩
slide-129-reduction-2 = app1 (fn value-N)

slide-129-reduction-3 : ∀ { s } → ⟨ (Fn: int ⇒ (N (+_ 7)) [ + ] (Var 0)) ＠ (N (+_ 5)) , s ⟩ ⟶ ⟨ N (+_ 7) [ + ] (N (+_ 5)) , s ⟩
slide-129-reduction-3 = fn value-N

slide-129-reduction-4 : ∀ { s } → ⟨ N (+_ 7) [ + ] (N (+_ 5)) , s ⟩ ⟶ ⟨ N (+_ 12) , s ⟩
slide-129-reduction-4 = op+


slide-152-example : Expression
slide-152-example =
  LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In (Var 0) ＠ N (+_ 3)

Δ = LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (Var 1) [ ≥ ] N (1ℤ) Then (Var 1) [ + ] (Var 0) ＠ ((Var 1) [ + ] (N ( -1ℤ ))) Else N (+_ 0)

slide-152-reduction-1 : ∀ {s} →
  ⟨ LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In (Var 0) ＠ N (+_ 3) , s ⟩ ⟶ ⟨ (Fn: int ⇒ Δ) ＠ N (+_ 3) , s ⟩
slide-152-reduction-1 = letrecfn

slide-152-reduction-2 : ∀ {s} →
  ⟨ (Fn: int ⇒ Δ) ＠ N (+_ 3) , s ⟩ ⟶ ⟨ LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (N (+_ 3)) [ ≥ ] N (1ℤ) Then (N (+_ 3)) [ + ] (Var 0) ＠ ((N (+_ 3)) [ + ] (N ( -1ℤ ))) Else N (+_ 0) , s ⟩
slide-152-reduction-2 = fn value-N

slide-152-reduction-3 : ∀ {s} → ⟨ LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (N (+_ 3)) [ ≥ ] N (1ℤ) Then (N (+_ 3)) [ + ] (Var 0) ＠ ((N (+_ 3)) [ + ] (N ( -1ℤ ))) Else N (+_ 0) , s ⟩ ⟶ ⟨ If (N (+_ 3)) [ ≥ ] N (1ℤ) Then (N (+_ 3)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 3)) [ + ] (N ( -1ℤ ))) Else N (+_ 0) , s ⟩
slide-152-reduction-3 = letrecfn

slide-152-reduction-4 : ∀ {s} → ⟨ If (N (+_ 3)) [ ≥ ] N (1ℤ) Then (N (+_ 3)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 3)) [ + ] (N ( -1ℤ ))) Else N (+_ 0) , s ⟩ ⟶ ⟨ If (B true) Then (N (+_ 3)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 3)) [ + ] (N ( -1ℤ ))) Else N (+_ 0) , s ⟩
slide-152-reduction-4 = if3 op≥

slide-152-reduction-5 : ∀ {s} → ⟨ If (B true) Then (N (+_ 3)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 3)) [ + ] (N ( -1ℤ ))) Else N (+_ 0) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 3)) [ + ] (N ( -1ℤ ))) , s ⟩
slide-152-reduction-5 = if1

slide-152-reduction-6 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 3)) [ + ] (N ( -1ℤ ))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] (Fn: int ⇒ Δ) ＠ (N (+_ 2)) , s ⟩
slide-152-reduction-6 = op2 value-N (app2 value-Fn op+)

slide-152-reduction-7 :  ∀ {s} → ⟨ (N (+_ 3)) [ + ] (Fn: int ⇒ Δ) ＠ (N (+_ 2)) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] (LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (N (+_ 2)) [ ≥ ] N (1ℤ) Then (N (+_ 2)) [ + ] (Var 0) ＠ ((N (+_ 2)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)) , s ⟩
slide-152-reduction-7 = op2 value-N (fn value-N)

slide-152-reduction-8 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] (LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (N (+_ 2)) [ ≥ ] N (1ℤ) Then (N (+_ 2)) [ + ] (Var 0) ＠ ((N (+_ 2)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] (If (N (+_ 2)) [ ≥ ] N (1ℤ) Then (N (+_ 2)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 2)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)) , s ⟩
slide-152-reduction-8 = op2 value-N letrecfn

slide-152-reduction-9 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] (If (N (+_ 2)) [ ≥ ] N (1ℤ) Then (N (+_ 2)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 2)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] (If (B true) Then (N (+_ 2)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 2)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)) , s ⟩
slide-152-reduction-9 = op2 value-N (if3 op≥)

slide-152-reduction-10 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] (If (B true) Then (N (+_ 2)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 2)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 2)) [ + ] (N ( -1ℤ )))) , s ⟩
slide-152-reduction-10 = op2 value-N if1

slide-152-reduction-11 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 2)) [ + ] (N ( -1ℤ )))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (Fn: int ⇒ Δ) ＠ (N (+_ 1))) , s ⟩
slide-152-reduction-11 = op2 value-N (op2 value-N (app2 value-Fn op+))

slide-152-reduction-12 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (Fn: int ⇒ Δ) ＠ (N (+_ 1))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (N (+_ 1)) [ ≥ ] N (1ℤ) Then (N (+_ 1)) [ + ] (Var 0) ＠ ((N (+_ 1)) [ + ] (N ( -1ℤ ))) Else N (+_ 0))) , s ⟩
slide-152-reduction-12 = op2 value-N (op2 value-N (fn value-N))

slide-152-reduction-13 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (N (+_ 1)) [ ≥ ] N (1ℤ) Then (N (+_ 1)) [ + ] (Var 0) ＠ ((N (+_ 1)) [ + ] (N ( -1ℤ ))) Else N (+_ 0))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (If (N (+_ 1)) [ ≥ ] N (1ℤ) Then (N (+_ 1)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 1)) [ + ] (N ( -1ℤ ))) Else N (+_ 0))) , s ⟩
slide-152-reduction-13 = op2 value-N (op2 value-N letrecfn)

slide-152-reduction-14 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (If (N (+_ 1)) [ ≥ ] N (1ℤ) Then (N (+_ 1)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 1)) [ + ] (N ( -1ℤ ))) Else N (+_ 0))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (If (B true) Then (N (+_ 1)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 1)) [ + ] (N ( -1ℤ ))) Else N (+_ 0))) , s ⟩
slide-152-reduction-14 = op2 value-N (op2 value-N (if3 op≥))

slide-152-reduction-15 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (If (B true) Then (N (+_ 1)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 1)) [ + ] (N ( -1ℤ ))) Else N (+_ 0))) , s ⟩ ⟶  ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 1)) [ + ] (N ( -1ℤ ))))) , s ⟩
slide-152-reduction-15 = op2 value-N (op2 value-N if1)

slide-152-reduction-16 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 1)) [ + ] (N ( -1ℤ ))))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (Fn: int ⇒ Δ) ＠ (N (+_ 0)))) , s ⟩
slide-152-reduction-16 = op2 value-N (op2 value-N (op2 value-N (app2 value-Fn op+)))

slide-152-reduction-17 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (Fn: int ⇒ Δ) ＠ (N (+_ 0)))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (N (+_ 0)) [ ≥ ] N (1ℤ) Then (N (+_ 0)) [ + ] (Var 0) ＠ ((N (+_ 0)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)))) , s ⟩
slide-152-reduction-17 = op2 value-N (op2 value-N (op2 value-N (fn value-N)))

slide-152-reduction-18 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (LetValRec: int ➝ int ≔[Fn⇒ If (Var 0) [ ≥ ] N (1ℤ) Then (Var 0) [ + ] (Var 1) ＠ ((Var 0) [ + ] (N ( -1ℤ ))) Else N (+_ 0) ]In If (N (+_ 0)) [ ≥ ] N (1ℤ) Then (N (+_ 0)) [ + ] (Var 0) ＠ ((N (+_ 0)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (If (N (+_ 0)) [ ≥ ] N (1ℤ) Then (N (+_ 0)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 0)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)))) , s ⟩
slide-152-reduction-18 = op2 value-N (op2 value-N (op2 value-N (letrecfn)))

slide-152-reduction-19 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (If (N (+_ 0)) [ ≥ ] N (1ℤ) Then (N (+_ 0)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 0)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (If (B false) Then (N (+_ 0)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 0)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)))) , s ⟩
slide-152-reduction-19 = op2 value-N (op2 value-N (op2 value-N (if3 op≥)))

slide-152-reduction-20 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] (If (B false) Then (N (+_ 0)) [ + ] (Fn: int ⇒ Δ) ＠ ((N (+_ 0)) [ + ] (N ( -1ℤ ))) Else N (+_ 0)))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] N (+_ 0))) , s ⟩
slide-152-reduction-20 = op2 value-N (op2 value-N (op2 value-N (if2)))

slide-152-reduction-21 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] ((N (+_ 1)) [ + ] N (+_ 0))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (N (+_ 1))) , s ⟩
slide-152-reduction-21 = op2 value-N (op2 value-N op+)

slide-152-reduction-22 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] ((N (+_ 2)) [ + ] (N (+_ 1))) , s ⟩ ⟶ ⟨ (N (+_ 3)) [ + ] (N (+_ 3)) , s ⟩
slide-152-reduction-22 = op2 value-N op+

slide-152-reduction-23 : ∀ {s} → ⟨ (N (+_ 3)) [ + ] (N (+_ 3)) , s ⟩ ⟶ ⟨ (N (+_ 6)) , s ⟩
slide-152-reduction-23 = op+
