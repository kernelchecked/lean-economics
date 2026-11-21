import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Okishio's theorem in one sector

This file formalizes the simplest one-sector case of Okishio's theorem
(Nobuo Okishio, 1961), in the same one-commodity setting as
`FundamentalMarxian.lean`: a single produced good, informally "corn,"
and, at any moment, one technique for producing it.

Okishio's theorem is a formal challenge to the falling-rate-of-profit
thesis. That thesis holds that the mechanization capitalists adopt in
pursuit of profit tends to depress the general rate of profit itself.
Okishio showed that, so long as the real wage does not change, this
cannot happen: a technical change that is worth adopting at current
prices can only raise the equilibrium rate of profit, never lower it.

## The model

All quantities are per unit of output:

- `a` is the input coefficient: the number of units of the good used up
  in producing one unit of output.
- `l` is the number of hours of labor required to produce one unit of
  output.
- `b` is the real wage, measured in units of the good paid per hour of
  labor. It is the SAME `b` for the old and the new technique: the real
  wage is held constant across the comparison, and that constancy is
  the heart of Okishio's assumption.

With the price of the good normalized to `1` and wages advanced, the
unit production cost of a technique is

`cost = a + b * l`:

the produced inputs plus the wage bill per unit of output.

The equilibrium (uniform) profit rate `r` of a technique solves the
price equation

`1 = (1 + r) * cost`,

so `r = (1 - cost) / cost`.

A new technique `(a', l')` is **viable** when it cuts unit cost at
current prices and the current real wage:

`a' + b * l' < a + b * l`.

Viability is exactly the condition that a profit-seeking producer would
voluntarily adopt the new technique: at the prices already ruling, it
produces the same unit more cheaply.

## The theorem

The theorem states that a viable technical change, at a constant real
wage, strictly raises the equilibrium profit rate:

**(1 - cost') / cost' > (1 - cost) / cost whenever cost' < cost.**

It assumes:

- nonnegative input coefficients, `0 ≤ a` and `0 ≤ a'`;
- positive labor inputs, `0 < l` and `0 < l'`;
- a nonnegative real wage, `0 ≤ b`, the same for both techniques;
- positive unit costs, `0 < a + b * l` and `0 < a' + b * l'`; and
- viability, `a' + b * l' < a + b * l`.

Note that the proof needs only the two positive costs and viability:
the conclusion holds whether or not the old profit rate was itself
positive.

## Limits

The scope is deliberately narrow, and the main limit is the theorem's
own famous caveat, stated rather than hidden. This is a model with ONE
produced good and ONE sector, and no prices beyond the normalization of
the good's price to `1`. Above all, the real wage `b` is constant BY
ASSUMPTION. If technical change is accompanied by a rising real wage,
the conclusion can fail; that case distinction — what happens to the
real wage as techniques change — is the substance of the subsequent
debate over the falling rate of profit, and it is not settled here.
The multi-sector Leontief version, with input matrices and
Perron–Frobenius theory, is future work and is not claimed here.
-/

/-- Okishio's theorem, one-sector case: fix the real wage `b`. If a new
technique `(a', l')` is viable — it lowers the unit cost
`a + b * l` at current prices and the current real wage — and both unit
costs are positive, then the new technique's equilibrium profit rate
`(1 - cost) / cost` is strictly higher than the old one. -/
theorem okishio_one_sector (a l a' l' b : ℝ)
    (ha : 0 ≤ a) (hl : 0 < l) (ha' : 0 ≤ a') (hl' : 0 < l') (hb : 0 ≤ b)
    (hcost : 0 < a + b * l) (hcost' : 0 < a' + b * l')
    (hviable : a' + b * l' < a + b * l) :
    (1 - (a + b * l)) / (a + b * l) < (1 - (a' + b * l')) / (a' + b * l') := by
  have hc : (a + b * l) ≠ 0 := ne_of_gt hcost
  have hc' : (a' + b * l') ≠ 0 := ne_of_gt hcost'
  -- The gain in the profit rate is the cost saving divided by the
  -- product of the two (positive) costs.
  have hdiff : (1 - (a' + b * l')) / (a' + b * l')
        - (1 - (a + b * l)) / (a + b * l)
      = ((a + b * l) - (a' + b * l')) / ((a + b * l) * (a' + b * l')) := by
    field_simp
    ring
  have hpos : 0 < (1 - (a' + b * l')) / (a' + b * l')
        - (1 - (a + b * l)) / (a + b * l) := by
    rw [hdiff]
    exact div_pos (by linarith) (mul_pos hcost hcost')
  linarith

-- Axioms audit: this should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms okishio_one_sector
