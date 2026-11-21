import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Instances.Real.Lemmas

open Filter
open scoped Topology

/-!
# The automation limit in two sectors

The automation-limit pair of `ExploitationLimit.lean` was proved in the
one-sector "corn" economy: as the labor input per unit of output tends
to zero, the rate of exploitation tends to infinity while the surplus
labor per unit of output tends to zero. This file proves the
multisector version of the same pair, in the two-sector Leontief
economy of `FundamentalMarxianTwoSector.lean`.

## The model

There are two produced goods, with input matrix entries `a b c d`:
producing one unit of good 1 uses `a` units of good 1 and `c` units of
good 2; producing one unit of good 2 uses `b` units of good 1 and `d`
units of good 2. The labor inputs per unit of output are `l1` and
`l2`, and one unit of labor is paid the consumption bundle `(u, v)`:
`u` units of good 1 and `v` units of good 2.

The labor values — labor embodied, directly and indirectly, in one
unit of each good — are given by Cramer's rule for the value
equations `lam = lam * A + l`:

- `lam1(x, y) = (x * (1 - d) + y * c) / J`,
- `lam2(x, y) = (x * b + y * (1 - a)) / J`,

where `J = (1 - a) * (1 - d) - b * c` and `(x, y)` are the labor
inputs. The *wage share* — the labor value of the consumption bundle
paid per unit of labor, i.e. the value of labor power — is

`w(x, y) = lam1(x, y) * u + lam2(x, y) * v`.

The rate of exploitation is `(1 - w) / w`: surplus labor over
necessary labor, per unit of labor.

## The scaling

Automation is modeled as scaling both sectors' labor inputs by a
common factor `t`: the labor inputs are `(t * l1, t * l2)` with the
input matrix and the wage bundle held fixed, and we let `t → 0` from
above. The key algebraic fact is that labor values are *linear* in
the labor inputs — Cramer's formulas are linear in `(x, y)` — so the
wage share scales exactly:

`w(t * l1, t * l2) = t * w(l1, l2)`

(`two_sector_wage_share_scale`, a pure algebra identity that needs no
hypotheses at all). Write `ŵ = w(l1, l2)` for the unscaled wage
share. Under the Hawkins–Simon productiveness conditions (`a < 1`,
`d < 1`, `J > 0`, nonnegative off-diagonal entries, positive labor
inputs, and a wage bundle with `u > 0`), the values are positive and
hence `ŵ > 0`.

## The limit pair

- **The rate of exploitation tends to infinity**
  (`two_sector_exploitation_rate_tendsto_atTop`). The rate at scale
  `t` is `(1 - t * ŵ) / (t * ŵ) = (t * ŵ)⁻¹ - 1`, and `t * ŵ → 0`
  from above, so the rate tends to `+∞` like `1 / t`. Necessary
  labor per unit of output vanishes quadratically in `t` — the labor
  embodied in the wage goods falls both because fewer hours are
  worked and because each hour's wage goods embody less labor —
  while total labor vanishes only linearly.

- **Total surplus labor per unit of gross output tends to zero**
  (`two_sector_surplus_labor_tendsto_zero`). Per unit of gross
  output — one unit of each good — the total labor performed at
  scale `t` is `t * (l1 + l2)` and the necessary labor is the wage
  share times that total, `w(t * l1, t * l2) * (t * (l1 + l2))`, so
  the surplus labor is `t * (l1 + l2) - ŵ * (l1 + l2) * t ^ 2`,
  which tends to `0`.

The measurement in the second statement matters, and we state it
honestly: surplus labor is measured *per unit of gross output*. Per
*hour worked*, the surplus share `1 - w` tends to `1`, not to `0`,
because the labor value of the wage bundle collapses along with `t`;
what vanishes is the total mass of surplus labor extracted per unit
of output, even as the rate of exploitation of each remaining hour
becomes unbounded. As in the one-sector file, the honest content is
the pair, not either half alone.

To our knowledge this exact multisector limit statement does not
appear in the literature: the one-sector pair is folklore made
precise in `ExploitationLimit.lean`, and the two-sector statement
here rests on the exact linearity of the Cramer formulas rather than
on any asymptotic argument.

## Limits

The scope is two sectors, with the values written out by Cramer's
rule; the general `n`-sector version would go through
Perron–Frobenius theory for the Leontief inverse instead. The input
matrix and the wage bundle are held fixed while the labor inputs
scale — nothing here describes a path along which the technique
itself, or the real wage bundle, changes as automation proceeds.
-/

/-- The wage share is homogeneous of degree one in the labor inputs:
scaling both sectors' labor inputs by `t` scales the wage share by
exactly `t`. This is pure algebra — the Cramer formulas for the
labor values are linear in the labor inputs — and needs no
hypotheses; it holds even where `J = 0`, both sides collapsing under
Lean's total division. -/
theorem two_sector_wage_share_scale (a b c d l1 l2 u v t : ℝ) :
    (((t * l1) * (1 - d) + (t * l2) * c) / ((1 - a) * (1 - d) - b * c)) * u
      + (((t * l1) * b + (t * l2) * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v
    = t * ((((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
      + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v)) := by
  have hN1 : (t * l1) * (1 - d) + (t * l2) * c = t * (l1 * (1 - d) + l2 * c) := by
    ring
  have hN2 : (t * l1) * b + (t * l2) * (1 - a) = t * (l1 * b + l2 * (1 - a)) := by
    ring
  rw [hN1, hN2, mul_div_assoc, mul_div_assoc]
  ring

/-- The rate of exploitation in the two-sector economy tends to
infinity as both sectors' labor inputs are scaled by `t → 0` from
above, with the input matrix and the wage bundle held fixed. Under
the Hawkins–Simon conditions the unscaled wage share `ŵ` is
positive, the rate at scale `t` is `(1 - t * ŵ) / (t * ŵ)`, and
`t * ŵ → 0` from above, so the rate blows up like `1 / t`. -/
theorem two_sector_exploitation_rate_tendsto_atTop (a b c d l1 l2 u v : ℝ)
    (h1a : a < 1) (h1d : d < 1) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hJ : 0 < (1 - a) * (1 - d) - b * c)
    (hl1 : 0 < l1) (hl2 : 0 < l2) (hu : 0 < u) (hv : 0 ≤ v) :
    Tendsto (fun t => (1 - ((((t * l1) * (1 - d) + (t * l2) * c)
        / ((1 - a) * (1 - d) - b * c)) * u
        + (((t * l1) * b + (t * l2) * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))
      / ((((t * l1) * (1 - d) + (t * l2) * c) / ((1 - a) * (1 - d) - b * c)) * u
        + (((t * l1) * b + (t * l2) * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))
      (𝓝[>] 0) atTop := by
  -- The unscaled wage share `ŵ` is positive: the first value `lam1`
  -- is positive (its numerator is positive and `J > 0`), the second
  -- value `lam2` is nonnegative, and the bundle has `u > 0`, `v ≥ 0`.
  have hlam1 : 0 < (l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c) := by
    apply div_pos _ hJ
    have h1 : 0 < l1 * (1 - d) := mul_pos hl1 (sub_pos.mpr h1d)
    have h2 : 0 ≤ l2 * c := mul_nonneg hl2.le hc
    linarith
  have hlam2 : 0 ≤ (l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c) := by
    apply div_nonneg _ hJ.le
    have h1 : 0 ≤ l1 * b := mul_nonneg hl1.le hb
    have h2 : 0 ≤ l2 * (1 - a) := mul_nonneg hl2.le (sub_nonneg.mpr h1a.le)
    linarith
  have hw : 0 < ((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
      + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v := by
    have h1 : 0 < ((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u :=
      mul_pos hlam1 hu
    have h2 : 0 ≤ ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v :=
      mul_nonneg hlam2 hv
    linarith
  -- By the scaling lemma, the rate at scale `t` is `(1 - t * ŵ) / (t * ŵ)`.
  have hfun : (fun t => (1 - ((((t * l1) * (1 - d) + (t * l2) * c)
        / ((1 - a) * (1 - d) - b * c)) * u
        + (((t * l1) * b + (t * l2) * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))
      / ((((t * l1) * (1 - d) + (t * l2) * c) / ((1 - a) * (1 - d) - b * c)) * u
        + (((t * l1) * b + (t * l2) * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))
      = (fun t => (1 - t * (((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
        + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))
      / (t * (((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
        + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))) := by
    funext t
    rw [two_sector_wage_share_scale]
  rw [hfun]
  -- `t * ŵ → 0` from above as `t → 0` from above, since `ŵ > 0`.
  have h1 : Tendsto (fun t => t * (((l1 * (1 - d) + l2 * c)
        / ((1 - a) * (1 - d) - b * c)) * u
        + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))
      (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hlim : Tendsto (fun t : ℝ => t * (((l1 * (1 - d) + l2 * c)
          / ((1 - a) * (1 - d) - b * c)) * u
          + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))
          (𝓝 0) (𝓝 (0 * (((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
          + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))) :=
        tendsto_id.mul tendsto_const_nhds
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hlim)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht hw
  -- Hence `(t * ŵ)⁻¹ → +∞`, and subtracting `1` preserves this.
  have h2 : Tendsto (fun t => (t * (((l1 * (1 - d) + l2 * c)
        / ((1 - a) * (1 - d) - b * c)) * u
        + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v))⁻¹ + -1)
      (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_inv_nhdsGT_zero.comp h1)
  -- On `0 < t`, `(1 - t * ŵ) / (t * ŵ) = (t * ŵ)⁻¹ + -1`. This is
  -- proved for a generic atom `x`, so that the inner divisions by
  -- `J` inside `ŵ` are never touched.
  have hident : ∀ x : ℝ, x ≠ 0 → (1 - x) / x = x⁻¹ + -1 := by
    intro x hx
    rw [sub_div, div_self hx, one_div, sub_eq_add_neg]
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hne : t * (((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
      + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v) ≠ 0 :=
    ne_of_gt (mul_pos ht hw)
  exact (hident _ hne).symm

/-- The other half of the two-sector automation limit: total surplus
labor per unit of gross output (one unit of each good) tends to zero
as both sectors' labor inputs are scaled by `t → 0` from above. The
total labor performed per unit of gross output is `t * (l1 + l2)`,
the necessary labor is the wage share at scale `t` times that total,
and by the scaling lemma the surplus is the polynomial
`(l1 + l2) * t - (ŵ * (l1 + l2)) * t ^ 2`, which is continuous with
value `0` at `t = 0`. No hypotheses are needed: this is the scaling
lemma plus continuity of a polynomial. -/
theorem two_sector_surplus_labor_tendsto_zero (a b c d l1 l2 u v : ℝ) :
    Tendsto (fun t => (t * (l1 + l2))
        - ((((t * l1) * (1 - d) + (t * l2) * c) / ((1 - a) * (1 - d) - b * c)) * u
          + (((t * l1) * b + (t * l2) * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v)
          * (t * (l1 + l2)))
      (𝓝[>] 0) (𝓝 0) := by
  have hfun : (fun t => (t * (l1 + l2))
        - ((((t * l1) * (1 - d) + (t * l2) * c) / ((1 - a) * (1 - d) - b * c)) * u
          + (((t * l1) * b + (t * l2) * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v)
          * (t * (l1 + l2)))
      = (fun t => (l1 + l2) * t
        - ((((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
          + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v)
          * (l1 + l2)) * t ^ 2) := by
    funext t
    rw [two_sector_wage_share_scale]
    ring
  rw [hfun]
  have h1 : Tendsto (fun t : ℝ => (l1 + l2) * t) (𝓝 0) (𝓝 ((l1 + l2) * 0)) :=
    tendsto_const_nhds.mul tendsto_id
  have h2 : Tendsto (fun t : ℝ => ((((l1 * (1 - d) + l2 * c)
        / ((1 - a) * (1 - d) - b * c)) * u
        + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v)
        * (l1 + l2)) * t ^ 2) (𝓝 0)
      (𝓝 (((((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
        + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v)
        * (l1 + l2)) * 0 ^ 2)) :=
    tendsto_const_nhds.mul (tendsto_id.pow 2)
  have hmain : Tendsto (fun t : ℝ => (l1 + l2) * t
        - ((((l1 * (1 - d) + l2 * c) / ((1 - a) * (1 - d) - b * c)) * u
          + ((l1 * b + l2 * (1 - a)) / ((1 - a) * (1 - d) - b * c)) * v)
          * (l1 + l2)) * t ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using h1.sub h2
  exact tendsto_nhdsWithin_of_tendsto_nhds hmain

-- Axioms audit: these should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms two_sector_wage_share_scale
#print axioms two_sector_exploitation_rate_tendsto_atTop
#print axioms two_sector_surplus_labor_tendsto_zero
