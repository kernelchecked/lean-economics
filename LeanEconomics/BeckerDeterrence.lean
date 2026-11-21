import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Classical

/-!
# Becker's economic model of crime: deterrence basics

This file formalizes the risk-neutral core of Gary Becker's 1968 economic
model of crime and punishment.

## The model

A potential offender gains `g > 0` from an offense. He is apprehended
with probability `p` and, if caught, bears a sanction of monetary
equivalent `f ≥ 0` (a fine, or the money value he attaches to another
punishment). His *expected net gain* from the offense is

`G(p, f, g) = (1 - p) * g - p * f`,

and, being risk neutral, he offends if and only if this expected gain is
positive. The expected gain is written out explicitly in every statement
below rather than hidden behind a definition.

## What is proved

- The two deterrence comparative statics for an individual: the expected
  gain is strictly decreasing in the apprehension probability `p`
  (`becker_gain_strictAnti_probability`) and strictly decreasing in the
  sanction `f` (`becker_gain_strictAnti_sanction`). The second result
  needs `0 < p`: severity can only bite when apprehension is possible at
  all.
- The offense condition in threshold form (`becker_commit_iff`): the
  offender offends exactly when `p * f < (1 - p) * g`, i.e. when the
  expected sanction is less than the expected gain.
- The aggregate versions: in a finite population with heterogeneous
  gains, the number of offenders is nonincreasing in `p`
  (`becker_offenders_card_anti_probability`) and nonincreasing in `f`
  (`becker_offenders_card_anti_sanction`). Together these say that
  Becker's *supply of offenses* `O(p, f, ·)` is decreasing in both of its
  policy arguments, in finite-population form.

## Limits

The scope is deliberately narrow:

- *Risk neutrality.* Everything is expected *value*, not expected
  *utility*. Becker's analysis with a concave utility function — where
  offenders are risk averse and probability and severity are no longer
  interchangeable — is separate future work.
- *Exogenous policy.* The probability `p` and the sanction `f` are taken
  as given. There is no enforcement-cost or social-loss optimization
  here: Becker's analysis of the *optimal* fine and probability is
  future work.
- *Monetary-equivalent sanctions.* The sanction is a single number, so
  fines and imprisonment are not distinguished.
- *Fixed gains.* Individuals' gains are heterogeneous across the
  population but do not themselves respond to `p` or `f`.
-/

/-- Deterrence through probability: with the gain `g > 0` and the
sanction `f ≥ 0` fixed, raising the apprehension probability strictly
lowers the expected net gain `(1 - p) * g - p * f` from an offense. -/
theorem becker_gain_strictAnti_probability (g f p₁ p₂ : ℝ) (hg : 0 < g) (hf : 0 ≤ f)
    (h : p₁ < p₂) :
    (1 - p₂) * g - p₂ * f < (1 - p₁) * g - p₁ * f := by
  have key : (1 - p₁) * g - p₁ * f - ((1 - p₂) * g - p₂ * f) = (p₂ - p₁) * (g + f) := by
    ring
  have hpos : 0 < (p₂ - p₁) * (g + f) := mul_pos (sub_pos.mpr h) (by linarith)
  linarith

/-- Deterrence through severity: with the apprehension probability
`p > 0` fixed, raising the sanction strictly lowers the expected net
gain `(1 - p) * g - p * f` from an offense. The hypothesis `0 < p` is
essential: if apprehension is impossible, the size of the sanction is
irrelevant. -/
theorem becker_gain_strictAnti_sanction (g f₁ f₂ p : ℝ) (hp : 0 < p) (h : f₁ < f₂) :
    (1 - p) * g - p * f₂ < (1 - p) * g - p * f₁ := by
  have key : (1 - p) * g - p * f₁ - ((1 - p) * g - p * f₂) = p * (f₂ - f₁) := by
    ring
  have hpos : 0 < p * (f₂ - f₁) := mul_pos hp (sub_pos.mpr h)
  linarith

/-- The offense condition: a risk-neutral potential offender offends —
his expected net gain `(1 - p) * g - p * f` is positive — if and only if
the expected sanction `p * f` is less than the expected gain
`(1 - p) * g`. -/
theorem becker_commit_iff (g f p : ℝ) :
    (0 < (1 - p) * g - p * f) ↔ p * f < (1 - p) * g := by
  constructor <;> intro h <;> linarith

/-- The supply of offenses is nonincreasing in the apprehension
probability: in a finite population `s` whose members have nonnegative
gains `g i`, raising the probability from `p₁` to `p₂ ≥ p₁` (sanction
`f ≥ 0` fixed) cannot increase the number of offenders, i.e. the number
of members whose expected net gain is positive. -/
theorem becker_offenders_card_anti_probability {ι : Type*} (s : Finset ι) (g : ι → ℝ) (f : ℝ)
    (hf : 0 ≤ f) (hg : ∀ i ∈ s, 0 ≤ g i) (p₁ p₂ : ℝ) (hp : p₁ ≤ p₂) :
    (s.filter (fun i => 0 < (1 - p₂) * g i - p₂ * f)).card ≤
    (s.filter (fun i => 0 < (1 - p₁) * g i - p₁ * f)).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  obtain ⟨his, hi2⟩ := hi
  refine ⟨his, ?_⟩
  have key : (1 - p₁) * g i - p₁ * f - ((1 - p₂) * g i - p₂ * f) = (p₂ - p₁) * (g i + f) := by
    ring
  have hnn : 0 ≤ (p₂ - p₁) * (g i + f) :=
    mul_nonneg (sub_nonneg.mpr hp) (add_nonneg (hg i his) hf)
  linarith

/-- The supply of offenses is nonincreasing in the sanction: in a finite
population `s`, raising the sanction from `f₁` to `f₂ ≥ f₁`
(apprehension probability `p ≥ 0` fixed) cannot increase the number of
offenders, i.e. the number of members whose expected net gain is
positive. -/
theorem becker_offenders_card_anti_sanction {ι : Type*} (s : Finset ι) (g : ι → ℝ) (p : ℝ)
    (hp : 0 ≤ p) (f₁ f₂ : ℝ) (hf : f₁ ≤ f₂) :
    (s.filter (fun i => 0 < (1 - p) * g i - p * f₂)).card ≤
    (s.filter (fun i => 0 < (1 - p) * g i - p * f₁)).card := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  obtain ⟨his, hi2⟩ := hi
  refine ⟨his, ?_⟩
  have key : (1 - p) * g i - p * f₁ - ((1 - p) * g i - p * f₂) = p * (f₂ - f₁) := by
    ring
  have hnn : 0 ≤ p * (f₂ - f₁) := mul_nonneg hp (sub_nonneg.mpr hf)
  linarith

-- Axioms audit: these should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms becker_gain_strictAnti_probability
#print axioms becker_gain_strictAnti_sanction
#print axioms becker_commit_iff
#print axioms becker_offenders_card_anti_probability
#print axioms becker_offenders_card_anti_sanction
