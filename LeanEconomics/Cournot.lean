import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Cournot competition and the Lerner index, with linear demand

This file formalizes the oldest model of oligopoly: Cournot competition
(Antoine Augustin Cournot, 1838) with linear inverse demand, together
with the Lerner index identity (Abba Lerner, 1934) evaluated at the
symmetric equilibrium. To our knowledge this is the first formalization
of the Cournot–Lerner results in any proof assistant; the results
themselves are classical.

## The model

Inverse demand is linear: when total output is `Q`, the market price is

`P = A - B * Q`,

with `A B : ℝ`. There are `n` firms, each with the same constant
marginal cost `c` and no fixed costs. A firm whose rivals produce `q`
each — `(n - 1) * q` in total — and which produces `x` itself earns the
profit

`(A - B * ((n - 1) * q + x) - c) * x`:

price minus marginal cost, times its own output. In the algebraic
theorems (`cournot_deviation_loss`, `cournot_best_response`,
`cournot_best_response_unique`) the firm count `n` is a real parameter;
only in the equilibrium and Lerner theorems is it a natural number, with
the casts written out in full.

The candidate symmetric equilibrium quantity is

`q* = (A - c) / (B * (n + 1))`,

the quantity at which every firm's first-order condition holds when all
rivals produce `q*` too: `A - c = B * (n + 1) * q*`.

## The deviation-loss identity

Textbook treatments derive the best response by differentiating the
profit function and invoking second-order conditions. With linear
demand none of that is needed: the first-order condition is also
*sufficient*, by an exact algebraic identity. Against rivals producing
`q` each, producing `x` instead of `q` changes the firm's profit by
exactly

`-B * (x - q) ^ 2`

(`cournot_deviation_loss`): the loss from any deviation is a perfect
square times `B`. The best-response property
(`cournot_best_response`) and its uniqueness
(`cournot_best_response_unique`) are immediate corollaries — the
identity *is* the second-order condition, with no calculus and no
hand-waving.

## The Lerner index

At the symmetric equilibrium with total output `n * q*` and price
`P = A - B * (n * q*)`, the markup satisfies

`P - c = B * q*`   and   `A - P = B * (n * q*)`,

so the Lerner index is

`(P - c) / P = 1 / (n * ε)`,   where `ε = P / (A - P)`

is the point elasticity of the linear demand at the equilibrium price
(`ε = -(dQ/dP) * (P / Q)` with `Q = (A - P) / B`). This is
`cournot_lerner`. The monopoly case is `n = 1`; as `n` grows the markup
shrinks like `1 / n`.

## What the formalization forced into the open

Writing these results with every hypothesis explicit surfaced several
points that the textbook statements leave implicit:

- **The best-response algebra needs no interiority.** Theorems 1–3 hold
  for *any* `q` satisfying the first-order equation `A - c = B * (n + 1)
  * q` — including a negative `q`, and with `n` an arbitrary real
  number. The first-order condition, the identity, and the uniqueness
  are pure algebra; economics enters only in deciding which solution
  is meaningful.
- **The closed form is a positive, economically meaningful equilibrium
  only under `c < A`.** If `c ≥ A`, the formula gives `q* ≤ 0`: there is
  no production at any price covering marginal cost, and the
  "equilibrium" is vacuous. The hypothesis `c < A` in
  `cournot_equilibrium` is used only to prove `q* > 0`; the
  best-response clauses hold for the first-order point regardless.
- **Uniqueness needs `B > 0` strictly.** At `B = 0` demand is perfectly
  elastic, the first-order condition forces `A = c`, every output earns
  zero profit, and *every* `x` is a best response — uniqueness fails
  outright, not just technically. (The non-strict best-response
  inequality survives at `B = 0`, as equality.)
- **The Lerner identity needs a positive price, and that is where
  `0 ≤ c` enters.** The proof obtains `P > 0` from the identity
  `P = c + B * q*`, using `c ≥ 0` and `B * q* > 0`. The textbook
  formula `(P - c) / P = 1 / (n * ε)` never mentions any condition on
  `c` at all; the formalization shows the identity is stated for a
  price that must first be known to be positive (and nonzero) before
  the ratio means anything.

## Limits

One homogeneous good, identical firms, constant marginal cost, linear
demand, quantities as continuous real numbers (outputs are not required
to be nonnegative in Theorems 1–3 — the algebra does not need it, and
the equilibrium theorem's `q* > 0` makes the constraint moot there).
Asymmetric costs, capacity constraints, Bertrand competition, and
general (nonlinear) demand — where the deviation-loss identity becomes
a genuine second-order condition and calculus is unavoidable — are
future work.
-/

/-- The deviation-loss identity: if `q` satisfies the first-order
condition `A - c = B * (n + 1) * q`, then a firm facing rivals who
produce `q` each and producing `x` itself earns exactly
`B * (x - q) ^ 2` less than it would by producing `q`. The difference of
the two profits is `(x - q)` times the first-order expression, which is
the whole proof. No sign hypothesis on `B` and no interiority is
needed: this is pure algebra. -/
theorem cournot_deviation_loss (A B c n q x : ℝ)
    (hFOC : A - c = B * (n + 1) * q) :
    (A - B * ((n - 1) * q + x) - c) * x
      = (A - B * ((n - 1) * q + q) - c) * q - B * (x - q) ^ 2 := by
  linear_combination (x - q) * hFOC

/-- `q` is a best response to rivals producing `q` each: no deviation
`x` earns more. By the deviation-loss identity the shortfall is
`B * (x - q) ^ 2`, which is nonnegative when `B ≥ 0`. -/
theorem cournot_best_response (A B c n q : ℝ) (hB : 0 ≤ B)
    (hFOC : A - c = B * (n + 1) * q) (x : ℝ) :
    (A - B * ((n - 1) * q + x) - c) * x
      ≤ (A - B * ((n - 1) * q + q) - c) * q := by
  have h := cournot_deviation_loss A B c n q x hFOC
  have hnn : 0 ≤ B * (x - q) ^ 2 := mul_nonneg hB (sq_nonneg _)
  linarith

/-- The best response is unique when `B > 0`: any deviation `x` that
does as well as `q` must equal `q`, since the deviation loss
`B * (x - q) ^ 2` is then strictly positive for `x ≠ q`. Strictness is
essential: at `B = 0` every output ties. -/
theorem cournot_best_response_unique (A B c n q : ℝ) (hB : 0 < B)
    (hFOC : A - c = B * (n + 1) * q) (x : ℝ)
    (hx : (A - B * ((n - 1) * q + x) - c) * x
      = (A - B * ((n - 1) * q + q) - c) * q) :
    x = q := by
  have h := cournot_deviation_loss A B c n q x hFOC
  have hsq : B * (x - q) ^ 2 = 0 := by linarith
  have h2 : (x - q) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hsq with hB0 | hsq0
    · exact absurd hB0 (ne_of_gt hB)
    · exact hsq0
  have h3 : x - q = 0 := by
    have := pow_eq_zero_iff (show (2 : ℕ) ≠ 0 by norm_num) |>.mp h2
    exact this
  exact sub_eq_zero.mp h3

/-- The symmetric Cournot equilibrium: for `n ≥ 1` firms, `B > 0` and
`c < A`, the quantity `q* = (A - c) / (B * (n + 1))` is positive, is a
best response to `n - 1` rivals each producing `q*`, and is the unique
such best response — i.e. the profile in which every firm produces `q*`
is a Nash equilibrium, and each firm's equilibrium output is the only
best reply to it. The hypothesis `c < A` is used only for the
positivity clause. -/
theorem cournot_equilibrium (A B c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hB : 0 < B) (hAc : c < A) :
    0 < (A - c) / (B * ((n : ℝ) + 1))
    ∧ (∀ x : ℝ, (A - B * (((n : ℝ) - 1) * ((A - c) / (B * ((n : ℝ) + 1))) + x) - c) * x
        ≤ (A - B * (((n : ℝ) - 1) * ((A - c) / (B * ((n : ℝ) + 1)))
          + ((A - c) / (B * ((n : ℝ) + 1)))) - c) * ((A - c) / (B * ((n : ℝ) + 1))))
    ∧ (∀ x : ℝ, (A - B * (((n : ℝ) - 1) * ((A - c) / (B * ((n : ℝ) + 1))) + x) - c) * x
        = (A - B * (((n : ℝ) - 1) * ((A - c) / (B * ((n : ℝ) + 1)))
          + ((A - c) / (B * ((n : ℝ) + 1)))) - c) * ((A - c) / (B * ((n : ℝ) + 1)))
        → x = (A - c) / (B * ((n : ℝ) + 1))) := by
  set q : ℝ := (A - c) / (B * ((n : ℝ) + 1)) with hq_def
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hBne : B * ((n : ℝ) + 1) ≠ 0 := ne_of_gt (mul_pos hB hn1)
  have hq_pos : 0 < q := div_pos (sub_pos.mpr hAc) (mul_pos hB hn1)
  have hFOC : A - c = B * ((n : ℝ) + 1) * q := by
    rw [hq_def]
    field_simp
  refine ⟨hq_pos, fun x => cournot_best_response A B c (n : ℝ) q hB.le hFOC x,
    fun x hx => cournot_best_response_unique A B c (n : ℝ) q hB hFOC x hx⟩

/-- The Lerner index at the symmetric Cournot equilibrium: with
`q* = (A - c) / (B * (n + 1))` and equilibrium price
`P = A - B * (n * q*)`, the markup ratio `(P - c) / P` equals
`1 / (n * ε)`, where `ε = P / (A - P)` is the point elasticity of the
linear demand at `P`. The hypothesis `0 ≤ c` is used only to show
`P > 0` (via `P = c + B * q*`), which the ratio needs before it means
anything. -/
theorem cournot_lerner (A B c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hB : 0 < B) (hc : 0 ≤ c) (hAc : c < A) :
    ((A - B * ((n : ℝ) * ((A - c) / (B * ((n : ℝ) + 1))))) - c)
      / (A - B * ((n : ℝ) * ((A - c) / (B * ((n : ℝ) + 1)))))
    = 1 / ((n : ℝ) * ((A - B * ((n : ℝ) * ((A - c) / (B * ((n : ℝ) + 1)))))
        / (A - (A - B * ((n : ℝ) * ((A - c) / (B * ((n : ℝ) + 1)))))))) := by
  set q : ℝ := (A - c) / (B * ((n : ℝ) + 1)) with hq_def
  set P : ℝ := A - B * ((n : ℝ) * q) with hP_def
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hBne : B * ((n : ℝ) + 1) ≠ 0 := ne_of_gt (mul_pos hB hn1)
  have hq_pos : 0 < q := div_pos (sub_pos.mpr hAc) (mul_pos hB hn1)
  have hFOC : A - c = B * ((n : ℝ) + 1) * q := by
    rw [hq_def]
    field_simp
  have hPc : P - c = B * q := by
    rw [hP_def]
    linear_combination hFOC
  have hAP : A - P = B * ((n : ℝ) * q) := by
    rw [hP_def]
    ring
  have hP_pos : 0 < P := by
    have hPeq : P = c + B * q := by linarith [hPc]
    rw [hPeq]
    exact add_pos_of_nonneg_of_pos hc (mul_pos hB hq_pos)
  have hAP_pos : 0 < A - P := by
    rw [hAP]
    exact mul_pos hB (mul_pos hnR hq_pos)
  have hRHS : 1 / ((n : ℝ) * (P / (A - P))) = (A - P) / ((n : ℝ) * P) := by
    field_simp
  rw [hRHS, hPc, hAP, div_eq_div_iff hP_pos.ne' (mul_pos hnR hP_pos).ne']
  ring

-- Axioms audit: these should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms cournot_deviation_loss
#print axioms cournot_best_response
#print axioms cournot_best_response_unique
#print axioms cournot_equilibrium
#print axioms cournot_lerner
