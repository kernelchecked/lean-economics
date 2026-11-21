# LeanEconomics

Formalizing economics results in Lean 4, using [Mathlib](https://github.com/leanprover-community/mathlib4) as a dependency. The aim is machine-checked proofs of economics theorems — every statement written with its assumptions explicit, and every proof checked by the Lean kernel with no admitted steps (`sorry`).

The starting area is Marxian and input-output economics — for example the Fundamental Marxian Theorem, Okishio's theorem, and the production-price / transformation problem, all of which rest on nonnegative matrices, Perron–Frobenius theory, and Leontief models. A verification review in November 2026 found no existing formalization of these results in Lean (or in any other proof assistant), so this is open ground.

## Status

Two theorems are proved so far, both with no `sorry` and `#print axioms` showing only the standard axioms:

- `LeanEconomics/ProfitRate.lean` — `profit_rate_lt_of_const_capital_lt`: with surplus value `s > 0` and variable capital `v ≥ 0` fixed, a larger constant capital gives a strictly lower profit rate `s / (c + v)`.
- `LeanEconomics/FundamentalMarxian.lean` — `fundamental_marxian_theorem_one_sector`: in a one-commodity model (input coefficient `a` with `0 ≤ a < 1`, labor input `l > 0`, real wage `b ≥ 0`), positive surplus labor is equivalent to a positive surplus product. The file states its scope limits (one good, one technique, no prices); the multi-sector Leontief version is future work.

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
