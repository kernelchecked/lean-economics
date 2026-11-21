import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The transformation problem: Bortkiewicz's counterexample

Marx's *Capital*, Vol. III, converts labor values into *prices of
production*: each sector's output sells at its cost price marked up by a
uniform rate of profit `r`. Marx asserted that this conversion preserves
two aggregate equalities, the *invariance postulates*:

- **(A) total price = total value**, and
- **(B) total profit = total surplus value**.

The *transformation problem* is whether (A) and (B) can both hold once
inputs, not just outputs, are bought at transformed prices. Ladislaus von
Bortkiewicz showed in 1907 that in general they cannot: the price system
has enough freedom to enforce one of the two equalities, but not both.
This file formalizes Bortkiewicz's three-department counterexample.

## The value scheme

Simple reproduction, three departments (I: means of production, II: wage
goods, III: luxuries). Each department advances constant capital `c` and
variable capital `v` and produces surplus value `s`; the rate of surplus
value `s / v = 2 / 3` is uniform, while the organic compositions `c / v`
differ across departments — that difference is what drives the result.

| Department | `c` | `v` | `s` | value |
|---|---|---|---|---|
| I (means of production) | 225 | 90 | 60 | 375 |
| II (wage goods) | 100 | 120 | 80 | 300 |
| III (luxuries) | 50 | 90 | 60 | 200 |
| **Total** | **375** | **300** | **200** | **875** |

## The price system

Department I's output is the input good bought as `c`, Department II's
output is the wage good bought as `v`, and Department III's output enters
no department's costs. Writing `x`, `y`, `z` for the price per unit of
value of the three departments' outputs, the prices of production with
uniform profit rate `r` satisfy

- `(225x + 90y)(1 + r) = 375x`,
- `(100x + 120y)(1 + r) = 300y`,
- `(50x + 90y)(1 + r) = 200z`.

## The result

The price system together with postulate (A) has the perfectly
consistent solution `x = 28/25`, `y = 14/15`, `z = 7/8`, `r = 1/4` (the
companion `example` below checks it by arithmetic). Under it the price
cost prices are `336`, `224`, `140` — a total of `700` — and the total
price is `875`, as (A) demands. But the total profit is then
`875 − 700 = 175 ≠ 200`: postulate (B) **fails**.

The theorem below proves this is forced, not an accident of the chosen
normalization: *any* positive multipliers `x, y, z` and profit rate `r`
satisfying the three price equations and postulate (A) give a total
profit different from the total surplus value `200`. (The proof pins
down `y = 5x / 6` and `1 + r = 5 / 4` from the first two equations; the
summed price equations then fix total cost price at `700`.)

## Limits

This is ONE concrete economy. A counterexample disproves the universal
claim that both equalities always hold; it does not by itself
characterize when they can hold. They do hold in the one-sector models
of the sibling files, and in multi-sector models under special
conditions such as equal organic compositions across departments. The
general `n`-sector characterization is future work and is not claimed
here.
-/

/-- Bortkiewicz's counterexample: in the three-department economy above,
any positive price multipliers `x, y, z` and uniform profit rate `r`
satisfying the three price-of-production equations and Marx's postulate
(A) (total price = total value, `875`) necessarily violate postulate
(B): the total profit differs from the total surplus value `200`. -/
theorem bortkiewicz_both_equalities_impossible (x y z r : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hr : 0 < r)
    (h1 : (225 * x + 90 * y) * (1 + r) = 375 * x)
    (h2 : (100 * x + 120 * y) * (1 + r) = 300 * y)
    (h3 : (50 * x + 90 * y) * (1 + r) = 200 * z)
    (hA : 375 * x + 300 * y + 200 * z = 875) :
    (375 * x + 300 * y + 200 * z)
      - ((225 * x + 90 * y) + (100 * x + 120 * y) + (50 * x + 90 * y)) ≠ 200 := by
  -- Step 1: eliminate `(1 + r)` between the first two price equations.
  -- Multiplying `h1` by Dept II's cost and `h2` by Dept I's cost makes
  -- the left sides equal, so `375x · (100x + 120y) = 300y · (225x + 90y)`.
  have elim : 375 * x * (100 * x + 120 * y) = 300 * y * (225 * x + 90 * y) := by
    calc 375 * x * (100 * x + 120 * y)
        = (225 * x + 90 * y) * (1 + r) * (100 * x + 120 * y) := by rw [h1]
      _ = (100 * x + 120 * y) * (1 + r) * (225 * x + 90 * y) := by ring
      _ = 300 * y * (225 * x + 90 * y) := by rw [h2]
  -- The resulting polynomial factors:
  -- `(6y − 5x)(4500y + 7500x) = 27000y² + 22500xy − 37500x² = 0`.
  have key : (6 * y - 5 * x) * (4500 * y + 7500 * x) = 0 := by
    linear_combination -elim
  -- The second factor is positive, so `6y = 5x`.
  have hfactor : (4500 * y + 7500 * x) ≠ 0 := ne_of_gt (by linarith)
  have h6y : 6 * y = 5 * x := by
    have h := (mul_eq_zero.mp key).resolve_right hfactor
    linarith
  have h90 : 90 * y = 75 * x := by linarith
  have h300 : 225 * x + 90 * y = 300 * x := by linarith
  -- Sum the three price equations and use postulate (A):
  -- total price cost, marked up by `(1 + r)`, equals total price `875`.
  have hsum : ((225 * x + 90 * y) + (100 * x + 120 * y) + (50 * x + 90 * y))
      * (1 + r) = 875 := by
    linear_combination h1 + h2 + h3 + hA
  -- Step 2: Dept I's cost is `300x` (using `90y = 75x`), so `h1` gives
  -- `300x (1 + r) = 375x`, and cancelling `x > 0` yields `1 + r = 5 / 4`.
  rw [h300] at h1
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx
  have h300r : 300 * (1 + r) = 375 := by
    apply mul_left_cancel₀ hxne
    linear_combination h1
  have hr14 : 1 + r = 5 / 4 := by linarith
  -- Step 3: hence total cost price is `875 / (5 / 4) = 700`, and the
  -- total profit is `875 − 700 = 175 ≠ 200`.
  rw [hr14] at hsum
  intro hcon
  linarith

/-- The price system plus postulate (A) is consistent: the exhibited
multipliers `x = 28/25`, `y = 14/15`, `z = 7/8` with `r = 1/4` satisfy
all three price equations and give total price `875`. The final conjunct
computes the resulting total profit: `175`, not `200` — so what fails in
this economy is exactly postulate (B), not the price system. -/
example : (225 * (28 / 25 : ℝ) + 90 * (14 / 15)) * (1 + 1 / 4) = 375 * (28 / 25)
    ∧ (100 * (28 / 25 : ℝ) + 120 * (14 / 15)) * (1 + 1 / 4) = 300 * (14 / 15)
    ∧ (50 * (28 / 25 : ℝ) + 90 * (14 / 15)) * (1 + 1 / 4) = 200 * (7 / 8)
    ∧ 375 * (28 / 25 : ℝ) + 300 * (14 / 15) + 200 * (7 / 8) = 875
    ∧ (375 * (28 / 25 : ℝ) + 300 * (14 / 15) + 200 * (7 / 8))
      - ((225 * (28 / 25 : ℝ) + 90 * (14 / 15))
        + (100 * (28 / 25 : ℝ) + 120 * (14 / 15))
        + (50 * (28 / 25 : ℝ) + 90 * (14 / 15))) = 175 := by
  norm_num

-- Axioms audit: this should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms bortkiewicz_both_equalities_impossible
