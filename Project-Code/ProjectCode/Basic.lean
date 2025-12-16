import Mathlib

-- Checks básicos (como los tuyos)
#check Prop
#check Type
#check Type 1
#check ℕ → Type

namespace Project

/-- DFA sobre un alfabeto Σ -/
structure MyDFA (sigma : Type u) where
  Q : Type v
  [fintype_Q : Fintype Q]
  δ : Q → sigma → Q
  q0 : Q
  F : Set Q

attribute [instance] MyDFA.fintype_Q

namespace MyDFA

variable {sigma : Type u} (M : MyDFA sigma)

-- δ* (función de transición extendida)
def step : M.Q → List sigma → M.Q
| q, []      => q
| q, a :: w  => step (M.δ q a) w

-- Aceptación
def accepts (w : List sigma) : Prop :=
  step M M.q0 w ∈ M.F

-- Lemas básicos (los que querías)
theorem step_nil (q : M.Q) : step M q [] = q := rfl
theorem step_q0_nil : step M M.q0 [] = M.q0 := rfl

end MyDFA

-- ===== EJEMPLO CONCRETO (tu myDFA) =====

def myDFA : Project.MyDFA Bool :=
{ Q := Fin 2
  δ := fun q a => if a then q else (q + 1)
  q0 := 0
  F := ({1} : Set (Fin 2)) }


-- Usar accepts como en tu ejemplo
open MyDFA

variable (w : List Bool)

#check accepts myDFA w
-- accepts myDFA w : Prop

-- Palabra vacía
theorem empty_word_accepted :
  step myDFA myDFA.q0 [] = myDFA.q0 := rfl

end Project
