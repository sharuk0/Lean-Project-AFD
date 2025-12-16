import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Pigeonhole


namespace Project

/-- DFA sobre un alfabeto sigma -/
structure DFA (sigma : Type u) where
    Q : Type u
    [fintype_Q : Fintype Q]
    δ : Q → sigma → Q
    q0 : Q
    F : Set Q

attribute [instance] DFA.fintype_Q

namespace DFA

variable {sigma : Type u} (M : DFA sigma)

-- δ* (función de transición extendida)
def step : M.Q → List sigma → M.Q
| q, []     => q
| q, a :: w => step (M.δ q a) w
-- Aceptación
def accepts (w : List sigma) : Prop :=
    step M M.q0 w ∈ M.F

-- Lenguaje que reconoce el DFA
def language : Set (List sigma) :=
    { w | M.accepts w }

@[simp] --simplicity lemma for step with list append
theorem step_append (q : M.Q) (w₁ w₂ : List sigma) :
  step M q (w₁ ++ w₂) = step M (step M q w₁) w₂ := by
  induction w₁ generalizing q <;> simp [step, *]

-- Lemas básicos
theorem step_nil (q : M.Q) : step M q [] = q := rfl
theorem step_q0_nil : step M M.q0 [] = M.q0 := rfl

end DFA

-- Lenguajes
abbrev Language (sigma : Type) := Set (List sigma)
def RegularLanguage (sigma : Type) (L : Language sigma) : Prop :=
    ∃ M : DFA sigma, L = M.language

/-- Potencia de una palabra: wordPow y i = y^i -/
def wordPow {σ : Type} (y : List σ) : ℕ → List σ
| 0     => []
| n+1   => y ++ wordPow y n

-- Helper lemmas
@[simp]
theorem wordPow_zero {σ : Type} (y : List σ) : wordPow y 0 = [] := rfl

@[simp]
theorem wordPow_succ {σ : Type} (y : List σ) (n : ℕ) :
  wordPow y (n + 1) = y ++ wordPow y n := rfl


-- Helper Lemma: Step distributes over power.
theorem step_pow {sigma : Type} (M : DFA sigma) (q : M.Q) (y : List sigma) (n : ℕ) :
  (DFA.step M q y = q) → DFA.step M q (wordPow y n) = q := by
  intro h
  induction n with
  | zero =>
    -- Case 0: step q [] = q. This is true by definition.
    rfl
  | succ n ih =>
    -- Case n+1: step q (y ++ y^n)
    rw [wordPow, DFA.step_append]
    rw [h]  -- Apply step q y = q
    exact ih

/-- Theorem: Pigeonhole principle for states -/
theorem pigeonhole_states {sigma : Type} (M : DFA sigma) (w : List sigma)
  (_ : w.length ≥ Fintype.card M.Q) :
  ∃ j l, j < l ∧ l ≤ Fintype.card M.Q ∧ -- Cardinalidad de elementos del set finito
    DFA.step M M.q0 (w.take j) = DFA.step M M.q0 (w.take l) := by
  let n := Fintype.card M.Q
  let f : Fin (n + 1) → M.Q := fun k => DFA.step M M.q0 (w.take k)
  -- 1. Cardinality check
  have h_card : Fintype.card (Fin (n + 1)) > Fintype.card M.Q := by
    simp only [Fintype.card_fin]
    exact Nat.lt_succ_self n
  -- 2. Apply Pigeonhole Principle
  have exists_collision := Fintype.exists_ne_map_eq_of_card_lt f h_card
  obtain ⟨a, b, h_ne, h_eq⟩ := exists_collision
  -- 3. Define j and l
  let j := min a b
  let l := max a b
  use j, l
  -- Goal 1: Prove j < l
  constructor
  · simp only [j, l]
    cases le_total a b with
    | inl h_le =>
      rw [min_eq_left h_le, max_eq_right h_le]
      -- Convert Fin inequality to Nat inequality
      exact lt_of_le_of_ne h_le (Fin.val_injective.ne h_ne)
    | inr h_le =>
      rw [min_eq_right h_le, max_eq_left h_le]
      exact lt_of_le_of_ne h_le (Fin.val_injective.ne h_ne.symm)
  -- Goal 2: Prove l ≤ card Q
  constructor
  · exact Nat.le_of_lt_succ l.2
  -- Goal 3: Prove steps are equal
  · dsimp [f] at h_eq
    simp only [j, l]
    cases le_total a b with
    | inl h_le =>
      rw [min_eq_left h_le, max_eq_right h_le]
      exact h_eq
    | inr h_le =>
      rw [min_eq_right h_le, max_eq_left h_le]
      exact h_eq.symm

/-- Theorem: Taking and dropping reconstructs the list -/
theorem take_drop_decomposition {α : Type} (w : List α) (j l : ℕ) (hjl : j < l) :
  w = w.take j ++ (w.drop j).take (l - j) ++ w.drop l := by
  conv_lhs =>
    -- 1. Split w into `take j` and `drop j`
    rw [← List.take_append_drop j w]
    -- 2. Focus on the right part (drop j w)
    rhs
    -- 3. Split it again
    rw [← List.take_append_drop (l - j) (w.drop j)]
    -- 4. Focus on the double drop
    rhs
    rw [List.drop_drop]
    -- 5. Fix the math in the index
    rw [Nat.add_comm, Nat.sub_add_cancel (le_of_lt hjl)]
  -- 6. Fix the parentheses/associativity mismatch
  -- This turns (A ++ B) ++ C into A ++ (B ++ C) or vice versa so they match.
  simp only [List.append_assoc]

/-- Theorem: Non-empty substring property -/
theorem nonempty_substring {α : Type} (w : List α) (j l : ℕ) (hjl : j < l) (hl : l ≤ w.length) :
  (w.drop j).take (l - j) ≠ [] := by
  -- A list is not empty if its length is > 0
  apply List.ne_nil_of_length_pos
  -- Calculate the length of the slice
  rw [List.length_take, List.length_drop]
  -- The length is min(l - j, length w - j). We need to show this min > 0.
  apply lt_min
  · -- Case 1: l - j > 0. True because j < l.
    exact Nat.sub_pos_of_lt hjl
  · -- Case 2: length w - j > 0. True because j < l ≤ length w.
    apply Nat.sub_pos_of_lt
    exact Nat.lt_of_lt_of_le hjl hl

/-- Theorem: Length bound for prefix -/
theorem length_bound {α : Type} (w : List α) (j l p : ℕ) (hjl : j ≤ l) (hl : l ≤ p) :
  (w.take j ++ (w.drop j).take (l - j)).length ≤ p := by
  -- We use the identity: take j w ++ take (l-j) (drop j w) = take (j + (l-j)) w
  -- This is known as `List.take_add` in Mathlib.
  rw [← List.take_add]
  -- Simplify the index: j + (l - j) = l
  rw [Nat.add_comm, Nat.sub_add_cancel hjl]
  -- Now we just need to show length (take l w) ≤ p
  rw [List.length_take]
  -- length (take l w) is min(l, length w), which is always ≤ l
  apply le_trans (min_le_left _ _)
  -- And we know l ≤ p from our hypothesis
  exact hl

/-- Theorem: Cycle property for DFA steps -/
theorem cycle_property {sigma : Type} (M : DFA sigma) (w : List sigma) (j l : ℕ) (hjl : j ≤ l)
  (heq : DFA.step M M.q0 (w.take j) = DFA.step M M.q0 (w.take l)) :
  DFA.step M (DFA.step M M.q0 (w.take j)) ((w.drop j).take (l - j)) =
  DFA.step M M.q0 (w.take j) := by
  -- 1. Rewrite the Right Hand Side using the hypothesis `heq`.
  --    We want the RHS to look like "step ... (take l)".
  --    (We use nth_rw 2 to target the RHS specifically)
  nth_rw 2 [heq]
  -- 2. Collapse the Left Hand Side nested steps into one sequence.
  --    Logic: step (step q A) B = step q (A ++ B)
  rw [← DFA.step_append]
  -- 3. Now we have: step M q0 (...list_expr...) = step M q0 (w.take l)
  --    It suffices to prove the lists are equal.
  congr 1
  -- 4. Use the list identity: take j ++ take n (drop j) = take (j + n)
  rw [← List.take_add]
  -- 5. Prove the arithmetic: j + (l - j) = l
  congr 1
  omega

/-- Theorem: Pumping preserves acceptance -/
theorem pumping_preserves_acceptance {sigma : Type} (M : DFA sigma)
  (x y z : List sigma) (i : ℕ)
  (hcycle : DFA.step M (DFA.step M M.q0 x) y = DFA.step M M.q0 x)
  (hw : DFA.step M M.q0 (x ++ y ++ z) ∈ M.F) :
  DFA.step M M.q0 (x ++ wordPow y i ++ z) ∈ M.F := by
  -- 1. Break down the goal state: step (x ++ y^i ++ z)
  --    We turn it into: step (step (step q0 x) y^i) z
  rw [DFA.step_append, DFA.step_append]
  -- 2. Apply the power lemma.
  --    We know `step q y = q` (from hcycle), so `step q y^i` must also be `q`.
  --    Here `q` is `DFA.step M M.q0 x`.
  rw [step_pow M (DFA.step M M.q0 x) y i hcycle]
  -- 3. Now the goal looks like: step (step q0 x) z ∈ F
  --    We just need to find this fact in `hw`.
  -- 4. Break down `hw`: step (x ++ y ++ z) ∈ F
  rw [DFA.step_append, DFA.step_append] at hw
  -- 5. Substitute the cycle in `hw`.
  --    Replace `step (step q0 x) y` with just `step q0 x`.
  rw [hcycle] at hw
  -- 6. Now `hw` matches our goal exactly.
  exact hw

/-- The Pumping Lemma  -/
theorem pumping_lemma {sigma : Type} {L : Language sigma} (hL : RegularLanguage sigma L) :
  ∃ p : ℕ,
    ∀ w ∈ L, w.length ≥ p →
      ∃ (x y z : List sigma),
        w = x ++ y ++ z ∧
        y ≠ [] ∧
        (x ++ y).length ≤ p ∧
        ∀ i, x ++ wordPow y i ++ z ∈ L := by
  -- Extract DFA from regularity assumption
  obtain ⟨M, hM⟩ := hL
  -- p is the number of states
  use Fintype.card M.Q
  --
  intro w hw hlen
  --
  -- w ∈ L means M accepts w
  rw [hM] at hw
  unfold DFA.language DFA.accepts at hw
  --
  -- Apply pigeonhole principle
  obtain ⟨j, l, hjl, hlp, hstates⟩ := pigeonhole_states M w hlen
  --
  -- Define x, y, z
  let x := w.take j
  let y := (w.drop j).take (l - j)
  let z := w.drop l
  --
  use x, y, z
  --
  constructor
  · -- w = x ++ y ++ z
    exact take_drop_decomposition w j l hjl
  --
  constructor
  · -- y ≠ []
    have hl_bound : l ≤ w.length := by omega
    exact nonempty_substring w j l hjl hl_bound
  --
  constructor
  · -- |xy| ≤ p
    exact length_bound w j l (Fintype.card M.Q) (le_of_lt hjl) hlp
  --
  · -- ∀ i, xy^i z ∈ L
    intro i
    rw [hM]
    unfold DFA.language DFA.accepts
  --
    -- Get cycle property
    have hcycle := cycle_property M w j l (le_of_lt hjl) hstates
  --
   -- Rewrite hw using w = x ++ y ++ z
    have hw' : DFA.step M M.q0 (x ++ y ++ z) ∈ M.F := by
      have : w = x ++ y ++ z := take_drop_decomposition w j l hjl
      rw [← this]
      exact hw
  --
    -- Apply pumping preservation
    exact pumping_preserves_acceptance M x y z i hcycle hw'

end Project

/- now we try using our lemma to prove that a^n b^m is not regular -/

/-a^n b^m-/



/-
  a^n b^m | n, m ≥ 0
inductive AB
| a
| b
deriving DecidableEq

open List

def repeat {α : Type} (x : α) : ℕ → List α
| 0     => []
| n+1   => x :: repeat x n


def aStarbStar : Language AB :=
  { w | ∃ n m : ℕ, w = repeat AB.a n ++ repeat AB.b m }



def aStarbStarDFA : DFA AB :=
{ Q := Fin 3
  δ := fun q s =>
    match q, s with
    | ⟨0, _⟩, AB.a => 0      -- seguimos leyendo a
    | ⟨0, _⟩, AB.b => 1      -- pasamos a b
    | ⟨1, _⟩, AB.b => 1      -- seguimos leyendo b
    | ⟨1, _⟩, AB.a => 2      -- error
    | ⟨2, _⟩, _    => 2      -- estado muerto
  q0 := 0
  F := {0, 1} }

-/
