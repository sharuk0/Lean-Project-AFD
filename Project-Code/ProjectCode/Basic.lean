import Mathlib
#check Prop
#check Type
#check Type 1

#check ℕ → Type

structure DFA (α : Type) :=
  (Q : Type)
  [finite_Q : Fintype Q]
  (δ : Q → α → Q)
  (q0 : Q)
  (F : Set Q)
