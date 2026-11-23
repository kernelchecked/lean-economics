import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Grossman–Stiglitz: the impossibility of informationally efficient markets

This file formalizes the paradox of Sanford J. Grossman and Joseph E.
Stiglitz, "On the Impossibility of Informationally Efficient Markets",
*American Economic Review* 70(3), June 1980, pp. 393–408 (JSTOR stable
URL 1805228). To our knowledge this is the first formalization of the
Grossman–Stiglitz paradox in any proof assistant.

## The argument being captured

Grossman and Stiglitz's general argument (their introduction and
Conjecture 6, the no-noise limit) is a pincer:

1. If the equilibrium price system *fully reveals* the payoff-relevant
   information, then a trader who paid for that information holds, at
   trading time, exactly the information every uninformed trader reads
   off the price for free. The gross return to being informed is zero,
   so at any positive information cost `c > 0` no trader optimally pays
   to become informed: there is no equilibrium with a positive fraction
   of informed traders and a fully revealing price.
2. If *nobody* is informed, no trader's demand carries the information,
   so the market-clearing price cannot reflect it: the price system is
   uninformative, and the information never enters the price at all.

Their resolution — an "equilibrium degree of disequilibrium", in which
*noise* in supply keeps prices only partially revealing so the informed
earn just enough to cover `c` — is the other half of the paper and is
deliberately **not** in this file (see "Limits" below).

## The model

The continuous CARA–Gaussian machinery of the paper's example is
replaced by the smallest trading problem in which the value of
information is *computed from optimal behaviour*, not postulated:

* `Θ` is a finite type of states (at least two), with weights
  `μ : Θ → ℝ`, `0 ≤ μ θ` — read `μ` as a prior. (Normalization
  `∑ θ, μ θ = 1` is never used by any statement below; the paradox does
  not turn on it, so it is not assumed.)
* One risky asset pays `v θ` in state `θ`; a riskless numéraire is the
  unit of account. The signal a trader may buy *is* the state `θ`
  itself (perfect information — the strongest, most favourable case for
  informational efficiency, and the case of GS's Conjecture 6).
* A *price system* is any function `p : Θ → ℝ`: the price that obtains
  when the state is `θ`. It is **fully revealing** if `p` is injective —
  observing the price is then logically equivalent to observing `θ`.
* A trader takes one position `a` from a fixed finite menu `A`
  (nonempty; think long/short/flat quantities) and earns
  `a * (v θ - p θ)` in state `θ` — the standard speculative gain of
  buying `a` units at `p θ` against payoff `v θ`.
* The **informed** trader observes `θ` before choosing, so her optimal
  expected gain is `informedValue`: in each state she picks the best
  position for that state. The **uninformed** trader observes only the
  price `p θ`, so her position may depend on `θ` only through the
  price: within each *fibre* of `p` (the states sharing one price) she
  must commit to a single position, chosen to maximize the
  `μ`-weighted gain over the fibre. That is `uninformedValue`. Both
  values are finite sums of finite maxima — no integrals, no Gaussians.

The one equilibrium condition used is the no-deviation condition for
the information decision itself: a positive fraction of informed
traders can be sustained only if a trader weakly prefers paying `c`
to trading uninformed, i.e. `uninformedValue ≤ informedValue - c`.

## What is proved

* `informedValue_eq_uninformedValue_of_injective`: under a fully
  revealing price the two values are *equal* — the gross benefit of
  the signal is exactly zero, derived here from the two optimizations,
  not assumed.
* `uninformedValue_le_informedValue`: information never hurts — the
  informed can always mimic any price-contingent strategy.
* `fully_revealing_supports_information_iff` (the headline): a fully
  revealing price supports costly information acquisition **if and
  only if `c ≤ 0`**. At `c > 0` this is the impossibility
  (`grossman_stiglitz_impossibility`, stated for an explicit
  information-equilibrium structure with a positive informed fraction);
  at `c = 0` the informed are merely indifferent, so the boundary is
  exactly the positivity of the cost — the formalization locates the
  edge of the theorem, as with the solvency boundary in
  `ModiglianiMiller.lean`.
* The `λ = 0` side, in reduced form: a price system that depends on
  no state information is a constant function, a constant price is not
  fully revealing (`not_injective_of_constant`), and under a constant
  price the uninformed problem collapses to the single no-price
  problem (`uninformedValue_of_constant`) — observing the price teaches
  literally nothing.

## Assumptions and limits (plain English)

* Price *formation* is not modelled: `p` is an arbitrary candidate
  price system, and the theorems say which price systems can coexist
  with optimal information acquisition. In the full GS model the price
  is pinned down by market clearing against random supply; deriving
  `p` rather than quantifying over it is a heavier model and is not
  attempted here.
* Correlatively, "if nobody is informed, the price cannot reflect θ"
  enters as the *definition* of the no-information case (a price
  formed from no state information is θ-independent, hence constant),
  not as a market-clearing derivation. This is the one place the file
  takes as a modelling primitive something GS derive.
* Traders are expected-payoff maximizers over a finite position menu:
  risk neutrality with position limits, in effect. GS's CARA traders
  and the utility-ratio formulation of their conjectures are not
  reproduced; the paradox's logic does not depend on risk aversion,
  and the finite-menu form is what makes the value of information a
  finite computation.
* The signal is perfect (it is the state). Noisy signals, random
  supply, partially revealing prices, and the *existence* of the noisy
  rational-expectations equilibrium — the constructive half of GS —
  are all left out.
* One asset, one period, no dynamics, no strategic (price-impact)
  behaviour: traders are price-takers facing the price system `p`.
-/

open Finset in
/-- The set of prices a price system `p` can take. -/
noncomputable def priceRange {Θ : Type} [Fintype Θ] (p : Θ → ℝ) : Finset ℝ :=
  Finset.image p Finset.univ

open Classical in
/-- The fibre of a price system over the price `q`: the states an
uninformed trader cannot distinguish after observing `q`. -/
noncomputable def fiber {Θ : Type} [Fintype Θ] (p : Θ → ℝ) (q : ℝ) : Finset Θ :=
  Finset.filter (fun θ => p θ = q) Finset.univ

section GrossmanStiglitz

variable {Θ : Type} [Fintype Θ] [DecidableEq Θ] [Nontrivial Θ]
variable {μ v p : Θ → ℝ} {A : Finset ℝ} (hA : A.Nonempty) {c : ℝ}

/-- The informed trader's optimal expected gain: knowing the state
`θ`, she chooses the position in `A` maximizing `a * (v θ - p θ)`, and
the gains are averaged with weights `μ`. -/
noncomputable def informedValue : ℝ :=
  ∑ θ, μ θ * Finset.sup' A hA (fun a => a * (v θ - p θ))

/-- The uninformed trader's optimal expected gain: she observes only
the price, so within each fibre of `p` she must commit to one position
from `A`, chosen to maximize the `μ`-weighted gain over that fibre;
the fibre gains are then totalled over all prices that occur. -/
noncomputable def uninformedValue : ℝ :=
  ∑ q ∈ priceRange p, Finset.sup' A hA
    (fun a => ∑ θ ∈ fiber p q, μ θ * (a * (v θ - p θ)))

/-- The no-deviation condition for the information decision: a trader
weakly prefers paying `c` to become informed over trading uninformed
at the same price system. A positive fraction of informed traders in
equilibrium requires this to hold. -/
def PaysForInformation : Prop :=
  uninformedValue (μ := μ) (v := v) (p := p) (A := A) hA ≤
    informedValue (μ := μ) (v := v) (p := p) (A := A) hA - c

/-- An information equilibrium: a price system, a positive fraction of
informed traders, and the no-deviation condition sustaining them. -/
structure InformationEquilibrium where
  /-- The equilibrium price system. -/
  price : Θ → ℝ
  /-- The fraction of traders who pay to become informed. -/
  fracInformed : ℝ
  /-- Somebody is informed. -/
  frac_pos : 0 < fracInformed
  /-- It is a fraction. -/
  frac_le_one : fracInformed ≤ 1
  /-- The informed do not want to deviate to uninformed. -/
  no_deviation :
    uninformedValue (μ := μ) (v := v) (p := price) (A := A) hA ≤
      informedValue (μ := μ) (v := v) (p := price) (A := A) hA - c

/-- Scaling a finite maximum by a nonnegative constant: the maximum of
`a ↦ k * f a` over `A` is `k` times the maximum of `f`. -/
lemma sup'_mul_of_nonneg {f : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k) :
    Finset.sup' A hA (fun a => k * f a) = k * Finset.sup' A hA f := by
  apply le_antisymm
  · exact Finset.sup'_le hA _ (fun a ha =>
      mul_le_mul_of_nonneg_left (Finset.le_sup' f ha) hk)
  · obtain ⟨a, ha, hfa⟩ := Finset.exists_mem_eq_sup' hA f
    rw [hfa]
    exact Finset.le_sup' (fun a => k * f a) ha

/-- The fibres of a price system partition the state space: summing a
function over each fibre, then over all prices that occur, is summing
it over all states. -/
lemma sum_priceRange_fiber (F : Θ → ℝ) :
    ∑ q ∈ priceRange p, ∑ θ ∈ fiber p q, F θ = ∑ θ, F θ := by
  unfold priceRange fiber
  exact Finset.sum_fiberwise_of_maps_to
    (fun θ _ => Finset.mem_image_of_mem p (Finset.mem_univ θ)) F

/-- Information never hurts: whatever the price system, the informed
trader's optimal expected gain is at least the uninformed trader's —
she can always mimic any price-contingent choice of position, and do
strictly better state-by-state whenever that helps. The only
hypothesis needed is that the weights are nonnegative. -/
theorem uninformedValue_le_informedValue (hμ : ∀ θ, 0 ≤ μ θ) :
    uninformedValue (μ := μ) (v := v) (p := p) (A := A) hA ≤
      informedValue (μ := μ) (v := v) (p := p) (A := A) hA := by
  unfold uninformedValue informedValue
  calc ∑ q ∈ priceRange p, Finset.sup' A hA
        (fun a => ∑ θ ∈ fiber p q, μ θ * (a * (v θ - p θ)))
      ≤ ∑ q ∈ priceRange p, ∑ θ ∈ fiber p q,
          μ θ * Finset.sup' A hA (fun a => a * (v θ - p θ)) := by
        apply Finset.sum_le_sum
        intro q _
        refine Finset.sup'_le hA _ (fun a ha => ?_)
        apply Finset.sum_le_sum
        intro θ _
        exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun a => a * (v θ - p θ)) ha) (hμ θ)
    _ = ∑ θ, μ θ * Finset.sup' A hA (fun a => a * (v θ - p θ)) :=
        sum_priceRange_fiber _

/-- The computational heart of the paradox. If the price system is
fully revealing — `p` injective, so the price tells the uninformed
exactly which state they are in — then the informed and uninformed
optimization problems coincide fibre by fibre (every fibre is a
singleton), and the two values are *equal*: the gross benefit of
having paid for the signal is exactly zero. -/
theorem informedValue_eq_uninformedValue_of_injective
    (hμ : ∀ θ, 0 ≤ μ θ) (hp : Function.Injective p) :
    informedValue (μ := μ) (v := v) (p := p) (A := A) hA =
      uninformedValue (μ := μ) (v := v) (p := p) (A := A) hA := by
  have hfiber : ∀ θ, fiber p (p θ) = {θ} := by
    intro θ
    ext θ'
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact hp.eq_iff
  have hfun : ∀ θ, (fun a => ∑ θ' ∈ fiber p (p θ), μ θ' * (a * (v θ' - p θ')))
      = (fun a => μ θ * (a * (v θ - p θ))) := by
    intro θ
    funext a
    rw [hfiber θ]
    exact Finset.sum_singleton _ _
  unfold uninformedValue informedValue priceRange
  rw [Finset.sum_image hp.injOn]
  apply Finset.sum_congr rfl
  intro θ _
  rw [hfun θ]
  exact (sup'_mul_of_nonneg hA (hμ θ)).symm

/-- **The exact boundary.** A fully revealing price system supports
information acquisition — the no-deviation condition holds — if and
only if the information is not costly, `c ≤ 0`. Positivity of the cost
is not an incidental hypothesis of the Grossman–Stiglitz theorem; it
is the whole theorem. -/
theorem fully_revealing_supports_information_iff
    (hμ : ∀ θ, 0 ≤ μ θ) (hp : Function.Injective p) :
    PaysForInformation (μ := μ) (v := v) (p := p) (A := A) hA (c := c) ↔ c ≤ 0 := by
  have heq : informedValue (μ := μ) (v := v) (p := p) (A := A) hA =
      uninformedValue (μ := μ) (v := v) (p := p) (A := A) hA :=
    informedValue_eq_uninformedValue_of_injective hA hμ hp
  unfold PaysForInformation
  rw [heq]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **The Grossman–Stiglitz impossibility.** If information costs
anything, `c > 0`, there is no information equilibrium with a positive
fraction of informed traders whose price system is fully revealing:
the informed would each strictly prefer to stop paying, read the
price, and trade exactly as well for free. -/
theorem grossman_stiglitz_impossibility
    (hμ : ∀ θ, 0 ≤ μ θ) (hc : 0 < c)
    (E : InformationEquilibrium (μ := μ) (v := v) (A := A) hA (c := c))
    (hrev : Function.Injective E.price) : False := by
  have heq : informedValue (μ := μ) (v := v) (p := E.price) (A := A) hA =
      uninformedValue (μ := μ) (v := v) (p := E.price) (A := A) hA :=
    informedValue_eq_uninformedValue_of_injective (p := E.price) hA hμ hrev
  have hnd := E.no_deviation
  linarith

/-- At zero cost the obstruction vanishes identically: for *every*
price system, revealing or not, the no-deviation condition holds —
the informed are at worst indifferent, because information never
hurts (`uninformedValue_le_informedValue`). Costless information is
the boundary case in which informationally efficient markets are not
ruled out by the paradox. -/
theorem zero_cost_supports_information (hμ : ∀ θ, 0 ≤ μ θ) :
    PaysForInformation (μ := μ) (v := v) (p := p) (A := A) hA (c := 0) := by
  unfold PaysForInformation
  rw [sub_zero]
  exact uninformedValue_le_informedValue hA hμ

/-- The other arm of the pincer, in reduced form. A constant price
system — the form a price takes when it is formed from no state
information at all, as when no trader is informed — is not fully
revealing: with at least two states, it cannot be injective. A price
that reflects nothing distinguishes nothing. -/
theorem not_injective_of_constant (q₀ : ℝ) (hp : ∀ θ, p θ = q₀) :
    ¬ Function.Injective p := by
  obtain ⟨a, b, hab⟩ := Nontrivial.exists_pair_ne (α := Θ)
  intro hinj
  exact hab (hinj ((hp a).trans (hp b).symm))

/-- Under a constant price, the uninformed trader's problem collapses
to the single problem of choosing one position against the prior with
no price observation at all: the one fibre is the whole state space.
Observing an uninformative price teaches nothing and is worth
nothing — the uninformed value is the no-information value. -/
theorem uninformedValue_of_constant (q₀ : ℝ) (hp : ∀ θ, p θ = q₀) :
    uninformedValue (μ := μ) (v := v) (p := p) (A := A) hA =
      Finset.sup' A hA (fun a => ∑ θ, μ θ * (a * (v θ - q₀))) := by
  obtain ⟨θ₀, -, -⟩ := Nontrivial.exists_pair_ne (α := Θ)
  have hprice : priceRange p = {q₀} := by
    ext q
    simp only [priceRange, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨θ, hθ⟩
      rw [← hθ]
      exact hp θ
    · intro hq
      exact ⟨θ₀, by rw [hp θ₀, hq]⟩
  have hfiber : fiber p q₀ = Finset.univ := by
    ext θ
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hp θ
  have hfun : (fun a => ∑ θ ∈ fiber p q₀, μ θ * (a * (v θ - p θ)))
      = (fun a => ∑ θ, μ θ * (a * (v θ - q₀))) := by
    funext a
    rw [hfiber]
    exact Finset.sum_congr rfl (fun θ _ => by rw [hp θ])
  unfold uninformedValue
  rw [hprice, Finset.sum_singleton, hfun]

end GrossmanStiglitz

#print axioms uninformedValue_le_informedValue
#print axioms informedValue_eq_uninformedValue_of_injective
#print axioms fully_revealing_supports_information_iff
#print axioms grossman_stiglitz_impossibility
#print axioms zero_cost_supports_information
#print axioms not_injective_of_constant
#print axioms uninformedValue_of_constant
