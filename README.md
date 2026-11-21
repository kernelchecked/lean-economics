# LeanEconomics

Formalizing economics results in Lean 4, using [Mathlib](https://github.com/leanprover-community/mathlib4) as a dependency. The aim is machine-checked proofs of economics theorems — every statement written with its assumptions explicit, and every proof checked by the Lean kernel with no admitted steps (`sorry`).

The starting area is Marxian and input-output economics — for example the Fundamental Marxian Theorem, Okishio's theorem, and the production-price / transformation problem, all of which rest on nonnegative matrices, Perron–Frobenius theory, and Leontief models. A verification review in November 2026 found no existing formalization of these results in Lean (or in any other proof assistant), so this is open ground.

## Status

Five results are proved so far, all with no `sorry` and `#print axioms` showing only the standard axioms:

- `LeanEconomics/ProfitRate.lean` — `profit_rate_lt_of_const_capital_lt`: with surplus value `s > 0` and variable capital `v ≥ 0` fixed, a larger constant capital gives a strictly lower profit rate `s / (c + v)`.
- `LeanEconomics/FundamentalMarxian.lean` — `fundamental_marxian_theorem_one_sector`: in a one-commodity model (input coefficient `a` with `0 ≤ a < 1`, labor input `l > 0`, real wage `b ≥ 0`), positive surplus labor is equivalent to a positive surplus product. The file states its scope limits (one good, one technique, no prices); the multi-sector Leontief version is future work.
- `LeanEconomics/FundamentalMarxianTwoSector.lean` — `fundamental_marxian_theorem_two_sector`: the Fundamental Marxian Theorem in a two-sector Leontief model — positive total surplus labor holds if and only if the wage-augmented input matrix `M = A + d ⊗ l` (produced inputs plus the wage goods workers consume) satisfies the Hawkins–Simon conditions, equivalently its Perron root is `< 1`, i.e. positive profit is possible. The proof runs through the determinant identity `det(I − M) = det(I − A)(1 − w)`, where `w` is the labor embodied in one hour's wage bundle.
- `LeanEconomics/Okishio.lean` — `okishio_one_sector`: Okishio's theorem in one sector — at a constant real wage, a viable (unit-cost-reducing) technical change strictly raises the equilibrium profit rate `(1 − cost) / cost`. The file states the constant-real-wage caveat plainly; the multi-sector version is future work.
- `LeanEconomics/TransformationProblem.lean` — `bortkiewicz_both_equalities_impossible`: in Bortkiewicz's three-department scheme (total value 875, total surplus value 200), any positive prices of production satisfying the price equations and Marx's postulate (A) (total price = total value) force total profit = 175 ≠ 200, so postulate (B) (total profit = total surplus value) cannot also hold. A companion example verifies the price system plus (A) is consistent (x = 28/25, y = 14/15, z = 7/8, r = 1/4). The general n-sector characterization of when both equalities can hold is future work.

Discussion: the project was announced on the Lean community Zulip, in the Project announcements stream — [“Formalizing Marxian economics in Lean — first results”](https://leanprover.zulipchat.com/#narrow/channel/579630-Project-announcements/topic/Formalizing.20Marxian.20economics.20in.20Lean.20.E2.80.94.20first.20results). Feedback is welcome there.

## Building

Requires the Lean toolchain via [elan](https://github.com/leanprover/elan). The toolchain version is pinned in `lean-toolchain`.

```sh
lake exe cache get   # download the prebuilt Mathlib cache (do not build Mathlib from source)
lake build
```

## Theorem naming

Theorems are named in Mathlib style (`snake_case`, descriptive of the result), e.g. a future `fundamental_marxian_theorem`, so results are findable by the names economists and Lean users would search for.

## License

Apache-2.0 — see `LICENSE`.

## GitHub configuration (from the project template)

To set up the GitHub repository after publishing:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
