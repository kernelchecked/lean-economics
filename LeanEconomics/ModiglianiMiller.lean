import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Modigliani–Miller: capital structure irrelevance, and its exact boundary

This file formalizes the two propositions of Franco Modigliani and
Merton H. Miller, "The Cost of Capital, Corporation Finance and the
Theory of Investment", *American Economic Review* 48(3), 1958,
pp. 261–297 — and then locates, exactly, the point at which their
arbitrage argument stops working.

## The model

Two firms generate identical cash flows. One is unlevered, with market
value `V_U`. The other carries perpetual debt `D` at interest rate
`r`, so it owes `r * D` per period; its equity has market value `E_L`
and its total value is `E_L + D`. An investor may hold any fraction
`α` of either firm's equity and may borrow at the same rate `r` as
the firm — the "homemade leverage" available in a perfect market.

## The arbitrage argument, made explicit

Proposition I — the value of the firm is independent of its capital
structure — rests on a replication. A fraction `α` of the levered
firm's equity pays `α * (X - r * D)` on cash flow `X`. An investor can
reproduce that payoff exactly without holding the levered firm at
all: borrow `α * D` at rate `r` and buy a fraction `α` of the
unlevered firm, for a payoff of `α * X - r * (α * D)`. The two
payoffs are equal (`mm_replication` — pure algebra). The homemade
position costs `α * (V_U - D)` (buy `α` of the unlevered firm, net of
the borrowing) while the levered position costs `α * E_L`; since the
payoffs coincide, the **law of one price** forces the costs to
coincide, and cancelling `α ≠ 0` gives `E_L + D = V_U`
(`mm_prop_one`). The law of one price is stated as a named hypothesis
of that theorem, not proved: it is the one economic assumption the
argument leans on, and this file names it rather than smuggling it in.

## The boundary the textbooks skip

The replication above is stated for a single sure cash flow. Make
the cash flow state-contingent and add limited liability, and the
replication has an exact edge. In a state with cash flow `X` and
promised payment `F`, levered equity pays `max (X - F) 0` — the
shareholders walk away from a shortfall — while the homemade strategy
pays `X - F` in full, because personal borrowing carries full
liability. The two payoffs coincide **if and only if** the firm is
solvent in that state (`mm_replication_iff_solvency`), and the
failure is not hypothetical: with cash flow `50` against a promised
payment of `100`, equity pays `0` and homemade leverage pays `-50`
(`mm_default_breaks_replication`). In default states the arbitrage
that proves Proposition I simply cannot be run; whether firm value
remains structure-independent there is a further question, not a
corollary.

## Proposition II

With total value `V = E + D`, write `r_E = (X - r * D) / E` for the
return on levered equity, `r_A = X / V` for the return on the firm's
assets, and `r_D = r` for the cost of debt. Proposition II — the
return on equity rises linearly with leverage — is then the identity
`r_E = r_A + (D / E) * (r_A - r_D)`, pure algebra given `V = E + D`
(`mm_prop_two`).

To our knowledge this is the first formalization of the
Modigliani–Miller propositions in any proof assistant — the theorem
appears on the Lean community's list of famous theorems not yet
formalized. The propositions themselves are classical.

## Limits

No taxes and no bankruptcy costs beyond the payoff truncation of
limited liability itself. Investors borrow at the firm's rate `r`.
The law of one price is assumed, as a named hypothesis. Values are
market values at a point in time; there is no dynamics, no growth,
and no equilibrium existence question — the file proves an arbitrage
identity, its consequence under the law of one price, and the exact
solvency boundary of the replication, nothing more.
-/

/-- The replication identity at the heart of Modigliani–Miller: the
homemade-leverage portfolio — borrow a fraction `α` of the levered
firm's debt `D` at rate `r` and hold a fraction `α` of the unlevered
firm — pays, per period on cash flow `X`, exactly what a fraction
`α` of the levered firm's equity pays. This is pure algebra; the
economic content is that the two positions are interchangeable. -/
theorem mm_replication (X D r α : ℝ) :
    α * X - r * (α * D) = α * (X - r * D) := by
  ring

/-- Modigliani–Miller Proposition I: the total value of the levered
firm, `E_L + D`, equals the value `V_U` of the unlevered firm. The
hypothesis `hLOP` is the law of one price applied to the two
portfolios of `mm_replication`: the levered-equity position costs
`α * E_L`, the homemade position costs `α * V_U - α * D =
α * (V_U - D)`, and equal payoffs force equal costs. The hypothesis
`α ≠ 0` is essential — at `α = 0` the comparison is vacuous and
nothing can be cancelled. -/
theorem mm_prop_one (V_U E_L D α : ℝ) (hα : α ≠ 0)
    (hLOP : α * E_L = α * (V_U - D)) :
    E_L + D = V_U := by
  have h : E_L = V_U - D := mul_left_cancel₀ hα hLOP
  linarith

/-- The exact boundary of the replication. In a state with cash flow
`X` and promised payment `F`, levered equity under limited liability
pays `max (X - F) 0`, while the homemade strategy — personal
borrowing, full liability — pays `X - F`. The two payoffs coincide
if and only if the firm is solvent in that state, `F ≤ X`. In
insolvent states the shareholders' walk-away option is worth
something, and the homemade portfolio cannot reproduce it. -/
theorem mm_replication_iff_solvency (X F : ℝ) :
    max (X - F) 0 = X - F ↔ F ≤ X := by
  constructor
  · intro h
    rcases le_total (X - F) 0 with hle | hle
    · -- Insolvent or break-even: `max (X - F) 0 = 0`, so the assumed
      -- equality forces `X - F = 0`.
      rw [max_eq_right hle] at h
      linarith
    · -- Solvent: `0 ≤ X - F` is exactly `F ≤ X`.
      linarith
  · intro h
    have h0 : 0 ≤ X - F := by linarith
    exact max_eq_left h0

/-- The exhibited default state: cash flow `50` against a promised
payment of `100`. Levered equity pays `0` — limited liability — while
the homemade strategy pays `-50`. The replication on which
Proposition I rests cannot be run in this state. -/
theorem mm_default_breaks_replication :
    max ((50 : ℝ) - 100) 0 ≠ (50 : ℝ) - 100 := by
  norm_num [max_eq_right]

/-- Modigliani–Miller Proposition II: the return on levered equity,
`r_E = (X - r * D) / E`, equals the return on the firm's assets plus
a leverage premium, `r_A + (D / E) * (r_A - r_D)`, where
`r_A = X / V` and `r_D = r`. Given Proposition I's conclusion in the
form `V = E + D`, this is pure algebra: leverage does not change the
total return to be divided, it only reallocates it, and the equity
return absorbs the whole reallocation. -/
theorem mm_prop_two (X D r E V : ℝ) (hV : V = E + D) (hE : E ≠ 0) (hV0 : V ≠ 0) :
    (X - r * D) / E = X / V + (D / E) * (X / V - r) := by
  field_simp
  linear_combination X * hV

-- Axioms audit: these should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms mm_replication
#print axioms mm_prop_one
#print axioms mm_replication_iff_solvency
#print axioms mm_default_breaks_replication
#print axioms mm_prop_two
