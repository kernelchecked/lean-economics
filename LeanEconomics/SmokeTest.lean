import Mathlib

/-!
# Smoke test

Build-environment smoke test for this project. These are elementary
examples that exercise the Mathlib import, the `omega` and `linarith`
tactics, and an axioms audit. They are **not** economics results.
-/

/-- Natural-number commutativity example, proved by `omega`. -/
theorem add_comm_example (a b : Nat) : a + b = b + a := by
  omega

/-- Real-number example, proved by `linarith`:
if `x < y` then `x + 1 < y + 1`. -/
theorem real_add_one_lt (x y : ℝ) (h : x < y) : x + 1 < y + 1 := by
  linarith

-- Axioms audit: this should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms add_comm_example
