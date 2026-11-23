# LeanEconomics

Formalizing economics results in Lean 4, using [Mathlib](https://github.com/leanprover-community/mathlib4) as a dependency. The aim is machine-checked proofs of economics theorems — every statement written with its assumptions explicit, and every proof checked by the Lean kernel with no admitted steps (`sorry`).

The starting area is Marxian and input-output economics, and the economics of crime, and the project now also covers corporate finance — for example the Fundamental Marxian Theorem, Okishio's theorem, and the production-price / transformation problem, all of which rest on nonnegative matrices, Perron–Frobenius theory, and Leontief models. A verification review in November 2026 found no existing formalization of these results in Lean (or in any other proof assistant), so this is open ground.

## Status

Thirteen results are proved so far, all with no `sorry` and `#print axioms` showing only the standard axioms:

- `LeanEconomics/ProfitRate.lean` — `profit_rate_lt_of_const_capital_lt`: with surplus value `s > 0` and variable capital `v ≥ 0` fixed, a larger constant capital gives a strictly lower profit rate `s / (c + v)`.
- `LeanEconomics/FundamentalMarxian.lean` — `fundamental_marxian_theorem_one_sector`: in a one-commodity model (input coefficient `a` with `0 ≤ a < 1`, labor input `l > 0`, real wage `b ≥ 0`), positive surplus labor is equivalent to a positive surplus product. The file states its scope limits (one good, one technique, no prices); the multi-sector Leontief version is future work.
- `LeanEconomics/FundamentalMarxianTwoSector.lean` — `fundamental_marxian_theorem_two_sector`: the Fundamental Marxian Theorem in a two-sector Leontief model — positive total surplus labor holds if and only if the wage-augmented input matrix `M = A + d ⊗ l` (produced inputs plus the wage goods workers consume) satisfies the Hawkins–Simon conditions, equivalently its Perron root is `< 1`, i.e. positive profit is possible. The proof runs through the determinant identity `det(I − M) = det(I − A)(1 − w)`, where `w` is the labor embodied in one hour's wage bundle.
- `LeanEconomics/Okishio.lean` — `okishio_one_sector`: Okishio's theorem in one sector — at a constant real wage, a viable (unit-cost-reducing) technical change strictly raises the equilibrium profit rate `(1 − cost) / cost`. The file states the constant-real-wage caveat plainly; the multi-sector version is future work.
- `LeanEconomics/TransformationProblem.lean` — `bortkiewicz_both_equalities_impossible`: in Bortkiewicz's three-department scheme (total value 875, total surplus value 200), any positive prices of production satisfying the price equations and Marx's postulate (A) (total price = total value) force total profit = 175 ≠ 200, so postulate (B) (total profit = total surplus value) cannot also hold. A companion example verifies the price system plus (A) is consistent (x = 28/25, y = 14/15, z = 7/8, r = 1/4). The general n-sector characterization of when both equalities can hold is future work.
- `LeanEconomics/ExploitationLimit.lean` — `exploitation_rate_tendsto_atTop` and `surplus_labor_tendsto_zero`: the automation limit in the one-sector model — as the labor input per unit `l → 0⁺` with `a < 1` and `b > 0` fixed, the rate of exploitation `(1 − a)/(b·l) − 1` tends to infinity (necessary labor vanishes like `l²`, surplus labor like `l`), while surplus labor per unit itself tends to zero.
- `LeanEconomics/BeckerDeterrence.lean` — Becker's 1968 economic model of crime in its risk-neutral core: the expected net gain from an offense, `(1 − p)·g − p·f`, is strictly decreasing in the apprehension probability `p` and in the sanction `f` (severity bites only when `p > 0`); the offense condition `p·f < (1 − p)·g`; and in a finite population the number of offenders — Becker's supply of offenses — is nonincreasing in both `p` and `f`.
- `LeanEconomics/BeckerOptimalFine.lean` — Becker's maximal-fine theorem: for a fixed deterrence target `p·f = D` with the fine bounded by the offender's wealth `W`, the cheapest policy is the corner `(D/W, W)` — maximal fine, minimal probability — because fines are transfers while enforcement cost rises with `p`; the corner policy is feasible exactly when `D ≤ W`, and with strictly increasing enforcement cost any interior fine is strictly more expensive.
- `LeanEconomics/OkishioWageThreshold.lean` — the Okishio wage threshold (`okishio_wage_threshold`): in the one-sector economy, a new technique evaluated at a possibly different real wage `b'` raises the equilibrium profit rate if and only if the wage increase `b' - b` is less than the old-wage unit cost saving divided by the new technique's labor input `l'`. Two corollaries: viability at the old wage makes the allowance strictly positive (`okishio_wage_allowance_pos`), and Okishio's constant-wage theorem is the `b' = b` case (`okishio_constant_wage`). To our knowledge this exact threshold characterization is new — the rising-wage caveat to Okishio's theorem is usually illustrated by examples rather than delimited by an if-and-only-if.
- `LeanEconomics/TwoSectorAutomationLimit.lean` — the automation limit in two sectors: the wage share is exactly homogeneous in the labor inputs (`two_sector_wage_share_scale`), so as both sectors' labor inputs scale by `t → 0⁺`, the rate of exploitation tends to infinity (`two_sector_exploitation_rate_tendsto_atTop`) while total surplus labor per unit of gross output tends to zero (`two_sector_surplus_labor_tendsto_zero`). The multisector generalization of the one-sector pair in `ExploitationLimit.lean`; to our knowledge this exact statement is also new.
- `LeanEconomics/Cournot.lean` — symmetric Cournot equilibrium with linear demand: the deviation-loss identity `π(x) = π(q) − B(x − q)²` (`cournot_deviation_loss`), the best response and its uniqueness (`cournot_best_response`, `cournot_best_response_unique`), the closed-form equilibrium quantity `q* = (A − c)/(B·(n + 1))` (`cournot_equilibrium`), and the Lerner identity `(P − c)/P = 1/(nε)` (`cournot_lerner`). A hypothesis audit accompanies the proofs: the condition `1 ≤ n` is essential for the Lerner identity (it fails at `n = 0`) but not for the equilibrium theorem, and the Lerner identity does not need `0 ≤ c`.
- `LeanEconomics/ModiglianiMiller.lean` — Modigliani & Miller (AER 1958): the homemade-leverage replication identity (`mm_replication`), Proposition I under the law of one price — stated as a named hypothesis, not proved (`mm_prop_one`) — Proposition II as a return identity (`mm_prop_two`), and the exact boundary of the replication: under limited liability, levered equity pays `max (X − F) 0` in a state while homemade leverage pays `X − F`, and the two payoffs coincide in a state if and only if the firm is solvent in it (`mm_replication_iff_solvency`), with a machine-checked default-state counterexample at `X = 50`, `F = 100` (`mm_default_breaks_replication`).
- `LeanEconomics/GrossmanStiglitz.lean` — the Grossman–Stiglitz impossibility of informationally efficient markets (AER 1980) in a finite-state model: a fully revealing price supports information acquisition if and only if the information cost satisfies `c ≤ 0` (`fully_revealing_supports_information_iff`), so at any cost `c > 0` no information equilibrium with a positive fraction of informed traders has a revealing price (`grossman_stiglitz_impossibility`). Companion results: information never hurts under any price system, at `c = 0` every price system supports acquisition, and under a constant price the uninformed problem collapses to the no-information problem. To our knowledge the first formalization of the Grossman–Stiglitz paradox in any proof assistant.

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
