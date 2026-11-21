import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Profit rate and constant capital

A first warm-up result about the Marxian profit rate.

Here `s` is surplus value, `v` is variable capital, and `c` is constant
capital, all modelled as real numbers. The profit rate on a capital with
constant part `c` is `s / (c + v)`.

The theorem below assumes surplus value is positive (`0 < s`), variable
capital is nonnegative (`0 ≤ v`), and the first constant capital is
positive (`0 < c₁`). It then proves ONLY one monotonicity fact: with `s`
and `v` held fixed, a strictly larger constant capital `c₂ > c₁` gives a
strictly smaller profit rate, `s / (c₂ + v) < s / (c₁ + v)`.

It says nothing about actual economies: no claim is made that `s` or `v`
really stay fixed when `c` changes, or that this formula describes any
real firm or country. It is purely the arithmetic of the formula.
-/

/-- Profit-rate monotonicity in constant capital: with surplus value `s`
and variable capital `v` fixed, a larger constant capital means a lower
profit rate `s / (c + v)`. -/
theorem profit_rate_lt_of_const_capital_lt (s v c₁ c₂ : ℝ)
    (hs : 0 < s) (hv : 0 ≤ v) (hc₁ : 0 < c₁) (h : c₁ < c₂) :
    s / (c₂ + v) < s / (c₁ + v) :=
  div_lt_div_of_pos_left hs (by linarith) (by linarith)

-- Axioms audit: this should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms profit_rate_lt_of_const_capital_lt
