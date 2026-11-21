import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A one-sector Fundamental Marxian Theorem

This file formalizes the Fundamental Marxian Theorem in the simplest
one-commodity setting: a single produced good, informally "corn," and one
technique for producing it.

All quantities are per unit of output:

- `a` is the input coefficient: the number of units of the good used up in
  producing one unit of output.
- `l` is the number of hours of labor required to produce one unit of
  output.
- `b` is the real wage, measured in units of the good paid per hour of
  labor.

The labor value of one unit of output is

`lam = l / (1 - a)`.

This is the labor embodied directly and indirectly in one unit: producing
the unit takes `l` hours, while replacing its produced inputs requires
still more labor through the same production process.

Workers receive `b * l` units of the good per unit of output, because one
unit requires `l` hours of labor and each hour is paid `b` units of the
good. The necessary labor per unit of output is therefore

`lam * (b * l)`,

the labor embodied in those wage goods. Surplus labor per unit is

`l - lam * (b * l)`.

The surplus product per unit is

`(1 - a) - b * l`:

one unit of output first replaces the `a` units used as input, and the
workers' wage goods are then deducted from the remaining net product.
Positivity of this surplus product is this model's form of positive
profit.

The theorem states that

**positive surplus labor if and only if positive surplus product
(this model's positive profit).**

Its assumptions are:

- a productive technique, `0 ≤ a < 1`;
- a positive labor input, `l > 0`; and
- a nonnegative real wage, `b ≥ 0`.

The scope is deliberately narrow. This is a model with ONE produced good
and ONE technique. It contains no prices or money and does not treat
joint production. The multi-sector Leontief version, with matrices and
Perron–Frobenius theory, is future work and is not claimed here.
-/

/-- The one-sector Fundamental Marxian Theorem: with a productive
technique (`0 ≤ a < 1`), positive labor input (`0 < l`), and a
nonnegative real wage (`0 ≤ b`), surplus labor is positive exactly when
the surplus product is positive. -/
theorem fundamental_marxian_theorem_one_sector (a l b : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hl : 0 < l) (hb : 0 ≤ b) :
    (0 < l - (l / (1 - a)) * (b * l)) ↔ (0 < (1 - a) - b * l) := by
  have hd : 0 < 1 - a := by
    linarith
  have key : l - (l / (1 - a)) * (b * l)
      = l * ((1 - a) - b * l) / (1 - a) := by
    field_simp
  rw [key, div_pos_iff_of_pos_right hd, mul_pos_iff_of_pos_left hl]

-- Axioms audit: this should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms fundamental_marxian_theorem_one_sector
