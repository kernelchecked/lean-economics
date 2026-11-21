import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Fundamental Marxian Theorem in two sectors

This file formalizes the Fundamental Marxian Theorem for a two-sector
Leontief economy. It is the two-good analogue of the one-sector theorem in
`FundamentalMarxian.lean`: positive total surplus labor holds exactly when
positive profit is possible.

## The model

There are two produced goods and one technique per sector. All quantities
are per unit of output:

- `a11 a12 a21 a22` are the produced-input coefficients: `a_ij` is the
  number of units of good `i` used up in producing one unit of good `j`.
  All are nonnegative.
- `l1 l2` are the labor inputs: `l_j` hours of labor produce one unit of
  good `j`. Both are positive.
- `d1 d2` are the real wage bundle: one hour of labor is paid `d_i` units
  of good `i`. Both are nonnegative.

Because workers spend their wages on the two goods, the wage goods are
themselves inputs into production. The *augmented* input coefficients,
which count wage goods alongside produced inputs, are

`m_ij = a_ij + d_i * l_j`.

## Labor values

The labor values `lam1 lam2` (labor embodied, directly and indirectly, in
one unit of each good) satisfy the value equations

- `lam1 = lam1 * a11 + lam2 * a21 + l1`,
- `lam2 = lam1 * a12 + lam2 * a22 + l2`,

i.e. `lam = lam * A + l`, or `lam * (I - A) = l`. The theorem *assumes*
values satisfying these equations, together with the Hawkins–Simon
productiveness condition on `A`:

- `a11 < 1` and `(1 - a11) * (1 - a22) - a12 * a21 > 0`.

Under these assumptions the Leontief inverse exists, the values are the
unique solution of the value equations, and they are positive: the proof
below derives, by Cramer's rule in coordinates,

- `lam1 * detA = l1 * (1 - a22) + l2 * a21`,
- `lam2 * detA = l1 * a12 + l2 * (1 - a11)`,

where `detA = (1 - a11) * (1 - a22) - a12 * a21`, and the right-hand sides
are positive.

## Surplus labor and profit

The *value of labor power* per hour is

`w = lam1 * d1 + lam2 * d2`,

the labor embodied in one hour's wage bundle. At activity levels
`x1 x2 > 0`, the total labor performed is `L = l1 * x1 + l2 * x2`, and the
total surplus labor — labor performed beyond the labor embodied in the
wage goods consumed — is

`S = L - w * L = L * (1 - w)`.

On the price side, positive profit is possible exactly when the augmented
matrix `M` has Perron root `< 1`: then, and only then, there are positive
prices `p1 p2 > 0` and a profit rate `r > 0` with
`p_j = (1 + r) * (p_1 * m_1j + p_2 * m_2j)` for both sectors. For a
nonnegative `2 × 2` matrix, Perron root `< 1` is equivalent to the
Hawkins–Simon conditions on `I - M`:

- `1 - m_11 > 0` and `det (I - M) > 0`.

This equivalence between the Perron root, positive prices of production,
and the Hawkins–Simon conditions is the standard characterization for
nonnegative matrices and is stated here as context. What the Lean proof
establishes is the equivalence of positive surplus labor with the
Hawkins–Simon condition on `M` itself:

**positive total surplus labor if and only if `M` satisfies
Hawkins–Simon.**

## The key identity

Since `M = A + d ⊗ l` is a rank-one update of `A`, the matrix determinant
lemma gives, in coordinates,

`det (I - M) = det (I - A) * (1 - w)`.

With `det (I - A) > 0` assumed, this identity turns positivity of
`det (I - M)` into `w < 1`, which — since `L > 0` — is exactly positivity
of surplus labor. The remaining Hawkins–Simon condition, `1 - m_11 > 0`,
follows in the forward direction from the value equations: one has
`lam1 * (1 - a11) = lam2 * a21 + l1 ≥ l1`, hence
`d1 * l1 ≤ d1 * lam1 * (1 - a11) ≤ w * (1 - a11) < 1 - a11`.

## Limits

The scope is deliberately narrow. This is a TWO-sector model with
explicit `2 × 2` determinant formulas throughout; the general `n`-sector
version requires Perron–Frobenius theory in matrix generality and is
future work, not claimed here. There is a single technique per sector, no
joint production, and no fixed capital.
-/

/-- The two-sector Fundamental Marxian Theorem: in the two-good Leontief
model above, with values `lam1 lam2` satisfying the value equations and
the Hawkins–Simon productiveness condition on `A`, total surplus labor is
positive if and only if the augmented matrix `M` (produced inputs plus
wage goods) satisfies the Hawkins–Simon conditions — equivalently, its
Perron root is `< 1`, i.e. positive profit is possible. -/
theorem fundamental_marxian_theorem_two_sector
    (a11 a12 a21 a22 l1 l2 d1 d2 lam1 lam2 x1 x2 : ℝ)
    (ha11 : 0 ≤ a11) (ha12 : 0 ≤ a12) (ha21 : 0 ≤ a21) (ha22 : 0 ≤ a22)
    (hl1 : 0 < l1) (hl2 : 0 < l2)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (hx1 : 0 < x1) (hx2 : 0 < x2)
    (hlam1 : lam1 = lam1 * a11 + lam2 * a21 + l1)
    (hlam2 : lam2 = lam1 * a12 + lam2 * a22 + l2)
    (hA11 : a11 < 1)
    (hdetA : 0 < (1 - a11) * (1 - a22) - a12 * a21) :
    (0 < (l1 * x1 + l2 * x2) - (lam1 * d1 + lam2 * d2) * (l1 * x1 + l2 * x2)) ↔
    (0 < 1 - (a11 + d1 * l1) ∧
     0 < (1 - (a11 + d1 * l1)) * (1 - (a22 + d2 * l2)) - (a12 + d1 * l2) * (a21 + d2 * l1)) := by
  -- Total labor `L` is positive.
  have hL : 0 < l1 * x1 + l2 * x2 := add_pos (mul_pos hl1 hx1) (mul_pos hl2 hx2)
  have h111 : 0 < 1 - a11 := by linarith
  -- (L0) Productiveness of `A` also gives `1 - a22 > 0`.
  have h122 : 0 < 1 - a22 := by
    by_contra h
    rw [not_lt] at h
    have hle : (1 - a11) * (1 - a22) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h111.le h
    have hnn : 0 ≤ a12 * a21 := mul_nonneg ha12 ha21
    linarith
  -- (L1) Cramer's rule in coordinates: the values times `detA`.
  have hL1a : lam1 * ((1 - a11) * (1 - a22) - a12 * a21)
      = l1 * (1 - a22) + l2 * a21 := by
    linear_combination (1 - a22) * hlam1 + a21 * hlam2
  have hL1b : lam2 * ((1 - a11) * (1 - a22) - a12 * a21)
      = l1 * a12 + l2 * (1 - a11) := by
    linear_combination a12 * hlam1 + (1 - a11) * hlam2
  -- (L2) The values are positive.
  have hlam1pos : 0 < lam1 := by
    have hpos : 0 < lam1 * ((1 - a11) * (1 - a22) - a12 * a21) := by
      rw [hL1a]
      have h1 : 0 < l1 * (1 - a22) := mul_pos hl1 h122
      have h2 : 0 ≤ l2 * a21 := mul_nonneg hl2.le ha21
      linarith
    by_contra h
    rw [not_lt] at h
    have hle : lam1 * ((1 - a11) * (1 - a22) - a12 * a21) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h hdetA.le
    linarith
  have hlam2pos : 0 < lam2 := by
    have hpos : 0 < lam2 * ((1 - a11) * (1 - a22) - a12 * a21) := by
      rw [hL1b]
      have h1 : 0 ≤ l1 * a12 := mul_nonneg hl1.le ha12
      have h2 : 0 < l2 * (1 - a11) := mul_pos hl2 h111
      linarith
    by_contra h
    rw [not_lt] at h
    have hle : lam2 * ((1 - a11) * (1 - a22) - a12 * a21) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h hdetA.le
    linarith
  -- (L3) The determinant identity: `det (I - M) = det (I - A) * (1 - w)`.
  have hdetM : (1 - (a11 + d1 * l1)) * (1 - (a22 + d2 * l2))
        - (a12 + d1 * l2) * (a21 + d2 * l1)
      = ((1 - a11) * (1 - a22) - a12 * a21) * (1 - (lam1 * d1 + lam2 * d2)) := by
    have h1 : ((1 - a11) * (1 - a22) - a12 * a21) * (1 - (lam1 * d1 + lam2 * d2))
        = ((1 - a11) * (1 - a22) - a12 * a21)
          - d1 * (lam1 * ((1 - a11) * (1 - a22) - a12 * a21))
          - d2 * (lam2 * ((1 - a11) * (1 - a22) - a12 * a21)) := by
      ring
    rw [h1, hL1a, hL1b]
    ring
  -- (L4) From the first value equation: `lam1 * (1 - a11) = lam2 * a21 + l1`.
  have hL4 : lam1 * (1 - a11) = lam2 * a21 + l1 := by
    linear_combination hlam1
  -- Surplus labor factors as `L * (1 - w)`.
  have hS : (l1 * x1 + l2 * x2) - (lam1 * d1 + lam2 * d2) * (l1 * x1 + l2 * x2)
      = (l1 * x1 + l2 * x2) * (1 - (lam1 * d1 + lam2 * d2)) := by
    ring
  constructor
  · -- Forward: positive surplus labor gives Hawkins–Simon for `M`.
    intro hsurp
    rw [hS] at hsurp
    have hw : 0 < 1 - (lam1 * d1 + lam2 * d2) := by
      by_contra h
      rw [not_lt] at h
      have hle : (l1 * x1 + l2 * x2) * (1 - (lam1 * d1 + lam2 * d2)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hL.le h
      linarith
    have hdetMpos : 0 < (1 - (a11 + d1 * l1)) * (1 - (a22 + d2 * l2))
        - (a12 + d1 * l2) * (a21 + d2 * l1) := by
      rw [hdetM]
      exact mul_pos hdetA hw
    have h1m : 0 < 1 - (a11 + d1 * l1) := by
      have hstep1 : l1 ≤ lam1 * (1 - a11) := by
        rw [hL4]
        have hnn : 0 ≤ lam2 * a21 := mul_nonneg hlam2pos.le ha21
        linarith
      have hchain : d1 * l1 < 1 - a11 := by
        calc d1 * l1 ≤ d1 * (lam1 * (1 - a11)) :=
              mul_le_mul_of_nonneg_left hstep1 hd1
          _ = (lam1 * d1) * (1 - a11) := by ring
          _ ≤ (lam1 * d1 + lam2 * d2) * (1 - a11) := by
              apply mul_le_mul_of_nonneg_right _ h111.le
              have hnn : 0 ≤ lam2 * d2 := mul_nonneg hlam2pos.le hd2
              linarith
          _ < 1 * (1 - a11) := by
              apply mul_lt_mul_of_pos_right _ h111
              linarith
          _ = 1 - a11 := by ring
      linarith
    exact ⟨h1m, hdetMpos⟩
  · -- Backward: Hawkins–Simon for `M` gives positive surplus labor.
    rintro ⟨_h1m, hdetMpos⟩
    have hw : 0 < 1 - (lam1 * d1 + lam2 * d2) := by
      by_contra h
      rw [not_lt] at h
      have hle : ((1 - a11) * (1 - a22) - a12 * a21)
          * (1 - (lam1 * d1 + lam2 * d2)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hdetA.le h
      rw [← hdetM] at hle
      linarith
    rw [hS]
    exact mul_pos hL hw

-- Axioms audit: this should list only the standard axioms
-- (`propext`, `Classical.choice`, `Quot.sound`) and no `sorryAx`.
#print axioms fundamental_marxian_theorem_two_sector
