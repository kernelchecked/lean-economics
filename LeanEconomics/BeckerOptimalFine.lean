import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Becker's economic model of crime: the optimal fine

This file formalizes the optimal-enforcement step of Gary Becker's 1968
economic model of crime and punishment: among all policies delivering a
fixed deterrence level, the cheapest uses the *maximal* fine and the
*minimal* apprehension probability.

## The model

Fix a *deterrence target* `D > 0`: the expected sanction that policy is
required to deliver. A policy is a pair `(p, f)` — an apprehension
probability `p` and a fine `f` — that delivers the target, i.e.
`p * f = D`, with `0 < p`, `0 < f`, and `f ≤ W`, where `W` is the
offender's wealth, the largest fine that can actually be collected.

The two instruments are asymmetric in cost. A fine is a *transfer*: it
costs the offender exactly what it pays the state, so its net social
cost is zero. Raising the probability `p`, by contrast, consumes real
resources — police, courts, prisons. So the *enforcement cost* is a
function `C : ℝ → ℝ` of `p` alone, nondecreasing in `p`.

## What is proved

- `becker_max_fine_feasible`: the corner policy `(p₀, f₀) = (D / W, W)`
  — maximal fine, minimal probability — is a genuine policy whenever
  the target is feasible at all (`D ≤ W`): `D / W` is a positive
  probability, at most `1`, and it delivers exactly `D` when paired
  with the fine `W`.
- `becker_max_fine_optimal`: no feasible policy is cheaper than the
  corner policy. The reason is one line: any feasible `f ≤ W` forces
  `p ≥ D / W`, and enforcement cost is nondecreasing in `p`.
- `becker_max_fine_strict`: if enforcement cost is *strictly*
  increasing in `p`, then any policy with an interior fine `f < W` is
  strictly more expensive than the corner policy.

## Limits

The scope is deliberately narrow:

- *The target is given.* This is only the cost-minimization step of
  Becker's analysis. Choosing `D` itself — Becker's full social-loss
  minimization, trading the harm from offenses against enforcement
  cost — is not here.
- *Cost depends on `p` alone.* Apprehension and conviction effort are
  bundled into the single function `C`; the fine enters only through
  the deterrence constraint `p * f = D`.
- *The wealth bound is hard.* If `D > W`, no fine-based policy can
  deliver the target at all: even `p = 1` with `f = W` yields only `W`.
  This is Becker's own route to non-monetary sanctions — imprisonment
  enters the analysis precisely where fines run out, and unlike fines
  it is socially costly, which breaks the clean corner result.
- *Risk neutrality.* As in `BeckerDeterrence.lean`, deterrence is the
  expected sanction `p * f`; offenders are risk neutral.
-/

/-- The corner policy is feasible: if the deterrence target `D > 0`
satisfies `D ≤ W` (the offender's wealth), then the probability
`D / W` is a genuine probability — positive and at most `1` — and
paired with the maximal fine `W` it delivers exactly the target `D`. -/
theorem becker_max_fine_feasible (D W : ℝ) (hD : 0 < D) (hDW : D ≤ W) :
    0 < D / W ∧ D / W ≤ 1 ∧ (D / W) * W = D := by
  have hW : 0 < W := hD.trans_le hDW
  exact ⟨div_pos hD hW, (div_le_one hW).mpr hDW, div_mul_cancel₀ D (ne_of_gt hW)⟩

/-- Becker's maximal-fine theorem: among all policies `(p, f)`
delivering a fixed deterrence target `p * f = D` with fine bounded by
the offender's wealth `W`, the cheapest is the corner policy
`(D / W, W)` — the maximal fine with the minimal probability. The fine
is a transfer and costs society nothing; enforcement cost `C` depends
only on `p` and is nondecreasing, and every feasible policy has
`p ≥ D / W`. -/
theorem becker_max_fine_optimal (C : ℝ → ℝ) (hC : Monotone C)
    (D W p f : ℝ) (hD : 0 < D) (hDW : D ≤ W)
    (hp : 0 < p) (hf : 0 < f) (hfW : f ≤ W) (hpf : p * f = D) :
    C (D / W) ≤ C p := by
  have hW : 0 < W := hD.trans_le hDW
  have h1 : D ≤ p * W := by
    rw [← hpf]
    exact mul_le_mul_of_nonneg_left hfW hp.le
  have h2 : D / W ≤ p := (div_le_iff₀ hW).mpr h1
  exact hC h2

/-- The strict version: if enforcement cost is strictly increasing in
`p`, then any policy whose fine is interior (`f < W`) is strictly more
expensive than the corner policy `(D / W, W)`. -/
theorem becker_max_fine_strict (C : ℝ → ℝ) (hC : StrictMono C)
    (D W p f : ℝ) (hD : 0 < D) (hDW : D ≤ W)
    (hp : 0 < p) (hf : 0 < f) (hfW : f < W) (hpf : p * f = D) :
    C (D / W) < C p := by
  have hW : 0 < W := hD.trans_le hDW
  have h1 : D < p * W := by
    rw [← hpf]
    exact mul_lt_mul_of_pos_left hfW hp
  have h2 : D / W < p := (div_lt_iff₀ hW).mpr h1
  exact hC h2

-- Axioms audit: these should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms becker_max_fine_optimal
#print axioms becker_max_fine_feasible
#print axioms becker_max_fine_strict
