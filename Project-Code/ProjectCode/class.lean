import Mathlib

namespace Project

/-- DFA sobre un alfabeto σ (versión typeclass) -/
class DFA (σ : Type u) where
  Q : Type v
  [fintype_Q : Fintype Q]
  δ : Q → σ → Q
  q0 : Q
  F : Set Q

attribute [instance] MyDFA.fintype_Q

namespace MyDFA

variable {σ : Type u}

/-- δ* (transición extendida). Usa la instancia `[M : MyDFA σ]`. -/
def step [M : MyDFA σ] : M.Q → List σ → M.Q
| q, []      => q
| q, a :: w  => step (M.δ q a) w

/-- Aceptación. -/
def accepts [M : MyDFA σ] (w : List σ) : Prop :=
  step (M := M) M.q0 w ∈ M.F

-- Lemitas básicos
theorem step_nil [M : MyDFA σ] (q : M.Q) : step (M := M) q [] = q := rfl
theorem step_q0_nil [M : MyDFA σ] : step (M := M) (MyDFA.q0 (σ := σ)) [] = MyDFA.q0 (σ := σ) := rfl

end MyDFA

-- ===== EJEMPLO CONCRETO COMO INSTANCIA =====

instance myDFAInst : MyDFA Bool where
  Q := Fin 2
  δ := fun q a => if a then q else (q + 1)
  q0 := 0
  F := ({1} : Set (Fin 2))

open MyDFA

variable (w : List Bool)

#check accepts (σ := Bool) w
-- accepts (σ := Bool) w : Prop

theorem empty_word_accepted :
  step (σ := Bool) (M := myDFAInst) (MyDFA.q0 (σ := Bool)) [] = MyDFA.q0 (σ := Bool) := rfl

end Project
