import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Okishio wage threshold: how far can the real wage rise?

This file sharpens Okishio's theorem (`Okishio.lean`) by removing its
most famous assumption. Okishio's theorem holds the real wage fixed:
a viable technical change, at a *constant* real wage, strictly raises
the equilibrium profit rate. The literature on the falling rate of
profit notes that a *rising* real wage can overturn the conclusion,
and standard treatments support that caveat with numerical examples:
pick a new technique and a high enough new wage, and the profit rate
falls. What the examples do not give is the exact boundary between
the two regimes. This file proves that boundary.

## The model

The setting is the one-sector economy of `Okishio.lean`. All
quantities are per unit of output. The old technique `(a, l)` —
input coefficient `a`, labor input `l` — is evaluated at the old real
wage `b`, giving unit cost and equilibrium profit rate

`c = a + b * l`,   `r = (1 - c) / c`.

The new technique `(a', l')` is now evaluated at a possibly
*different* real wage `b'`, giving

`c' = a' + b' * l'`,   `r' = (1 - c') / c'`.

## The threshold

The main theorem is an exact characterization, with no viability
assumption and no constant-wage assumption: for positive unit costs
and `l' > 0`,

**the profit rate rises, `r < r'`, if and only if**
**`b' - b < ((a - a') + b * (l - l')) / l'`.**

The numerator on the right is the old-wage unit cost saving,
`(a + b * l) - (a' + b * l')` — the amount the new technique would
save per unit of output if the wage had stayed at `b`. So the
threshold says: the profit rate rises if and only if the real-wage
increase is less than the cost saving *per new hour of labor*. At
equality the profit rate is unchanged; above it, the profit rate
falls. To our knowledge this exact threshold characterization does
not appear in the literature: the rising-wage caveat to Okishio's
theorem is standard, but it is usually illustrated by example rather
than delimited by an if-and-only-if.

Two corollaries make the content concrete:

- If the new technique is viable at the old wage
  (`a' + b * l' < a + b * l`), the wage allowance is strictly
  positive: there is always *some* rise in the real wage that the
  innovation can absorb while still raising the profit rate
  (`okishio_wage_allowance_pos`).
- Okishio's original theorem is the special case `b' = b`: the wage
  increase is then `0`, which is below the positive allowance, so
  the profit rate rises (`okishio_constant_wage`). This recovers the
  conclusion of `okishio_one_sector` in `Okishio.lean` from the
  threshold theorem.

## Limits

The scope is the same one-sector economy as `Okishio.lean`: one
produced good, one technique change, the good's price normalized
to `1`. Positive unit costs are assumed throughout, since the rate
formula `(1 - c) / c` presupposes `c > 0`. The characterization is
about a single contemplated technique change at two given wages; it
says nothing about which wage path an economy actually follows,
and the multi-sector version is not claimed here.
-/

/-- The Okishio wage threshold: in the one-sector economy, with the
old technique `(a, l)` evaluated at the real wage `b` and the new
technique `(a', l')` evaluated at a possibly different real wage
`b'`, and both unit costs positive, the new technique's equilibrium
profit rate `(1 - c') / c'` strictly exceeds the old one `(1 - c) / c`
if and only if the real-wage increase `b' - b` is less than the
old-wage unit cost saving `(a + b * l) - (a' + b * l')` divided by
the new technique's labor input `l'`. -/
theorem okishio_wage_threshold (a l a' l' b b' : ℝ)
    (hc : 0 < a + b * l) (hc' : 0 < a' + b' * l') (hl' : 0 < l') :
    (1 - (a + b * l)) / (a + b * l) < (1 - (a' + b' * l')) / (a' + b' * l') ↔
    b' - b < ((a - a') + b * (l - l')) / l' := by
  have hc0 : (a + b * l) ≠ 0 := ne_of_gt hc
  have hc'0 : (a' + b' * l') ≠ 0 := ne_of_gt hc'
  -- For positive `x`, the profit rate `(1 - x) / x` is `x⁻¹ - 1`.
  have e1 : (1 - (a + b * l)) / (a + b * l) = (a + b * l)⁻¹ - 1 := by
    field_simp
  have e2 : (1 - (a' + b' * l')) / (a' + b' * l') = (a' + b' * l')⁻¹ - 1 := by
    field_simp
  -- Step A: since the rate is `1 / cost - 1`, strictly decreasing in
  -- the cost, the rate rises if and only if the cost falls.
  have stepA : (1 - (a + b * l)) / (a + b * l) < (1 - (a' + b' * l')) / (a' + b' * l')
      ↔ a' + b' * l' < a + b * l := by
    have hinv : (a + b * l)⁻¹ < (a' + b' * l')⁻¹ ↔ a' + b' * l' < a + b * l :=
      inv_lt_inv₀ hc hc'
    constructor
    · intro h
      rw [e1, e2] at h
      exact hinv.mp (by linarith)
    · intro h
      rw [e1, e2]
      have h2 := hinv.mpr h
      linarith
  -- Step B: the cost falls if and only if the wage increase, charged
  -- at the new technique's labor input, is less than the old-wage
  -- cost saving; dividing by `l' > 0` gives the threshold form.
  have stepB : a' + b' * l' < a + b * l
      ↔ (b' - b) * l' < (a - a') + b * (l - l') := by
    have key : (a + b * l) - (a' + b' * l')
        = ((a - a') + b * (l - l')) - (b' - b) * l' := by ring
    constructor <;> intro h <;> linarith
  exact stepA.trans (stepB.trans (lt_div_iff₀ hl').symm)

/-- The wage allowance is positive for a viable technique: if the
new technique `(a', l')` lowers the unit cost at the *old* real wage
`b`, then the threshold of `okishio_wage_threshold` — the old-wage
cost saving per new hour of labor — is strictly positive, so some
rise in the real wage is compatible with a rising profit rate. -/
theorem okishio_wage_allowance_pos (a l a' l' b : ℝ)
    (hl' : 0 < l') (hviable : a' + b * l' < a + b * l) :
    0 < ((a - a') + b * (l - l')) / l' := by
  have hnum : 0 < (a - a') + b * (l - l') := by
    have key : (a - a') + b * (l - l') = (a + b * l) - (a' + b * l') := by ring
    rw [key]
    linarith
  exact div_pos hnum hl'

/-- Okishio's theorem recovered from the threshold: if the new
technique `(a', l')` is viable at the *constant* real wage `b` and
both unit costs are positive, its equilibrium profit rate strictly
exceeds the old one. This is the `b' = b` case of
`okishio_wage_threshold`: the wage increase is `0`, which the
positive allowance of `okishio_wage_allowance_pos` exceeds. -/
theorem okishio_constant_wage (a l a' l' b : ℝ)
    (hc : 0 < a + b * l) (hc' : 0 < a' + b * l') (hl' : 0 < l')
    (hviable : a' + b * l' < a + b * l) :
    (1 - (a + b * l)) / (a + b * l) < (1 - (a' + b * l')) / (a' + b * l') := by
  apply (okishio_wage_threshold a l a' l' b b hc hc' hl').mpr
  simpa using okishio_wage_allowance_pos a l a' l' b hl' hviable

-- Axioms audit: these should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms okishio_wage_threshold
#print axioms okishio_wage_allowance_pos
#print axioms okishio_constant_wage
