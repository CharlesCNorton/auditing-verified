# Remaining gaps

All items compile-tested against Rocq 9.0 / MathComp 2.5 / MathComp Analysis 1.15. Zero Admitted.

1. Prove the conditional independence of `lr(x_n)` given `ballot_F(n)` under the product measure.
2. Prove `QR_add` for cross-denominator arguments.
3. Prove `uniform_mu_sum1` and `uniform_marginal` for the uniform product measure on `{ffun 'I_k -> bool}`.
4. Instantiate `events_fully_independent` using the uniform product measure.
5. Prove a general `min_k` correctness lemma linking `search_k` output to `(1-alpha)^k <= 1-delta` for arbitrary inputs.
6. Add a downstream proof that calls `partition_filtration`.

Items 1, 3, 4, 6 all converge on one technical kernel: decomposing sums over `{ffun 'I_N -> bool}` into coordinate-wise products when restricted to equivalence classes of the natural filtration. Once that factorization lemma exists, all four close immediately.

7. Prove the supermartingale inequality for `ballot_plr`: `E[ballot_plr(n+1) | F_n] <= ballot_plr(n)`. Adaptedness is proved (`ballot_plr_adapted`) and the factorization tool exists (`multiplicative_martingale_step`) but the two are never composed.
8. State and prove that the two-point distribution does NOT satisfy `events_independent` or `events_fully_independent`. `two_pt_product_gap` and `two_pt_dependence_gap` prove the numerical gap but never connect it to the probability-space independence definitions.
9. Prove `cond_exp` idempotency: `E[E[X|F_n] | F_n] = E[X|F_n]`. `cond_exp_measurable` handles adapted functions but general idempotency is absent.
10. Add submartingale-specific results: upward Doob inequality, upward Ville analogue. Currently only the definition and coercion from martingale exist.
11. Prove surjectivity of the grouping from `complement_chromatic_le_styles` so that `overlap_hetero_pipeline` can fire from the grouping alone without an external surjectivity proof.
12. Bundle `Hcell` (positive cell mass) into the `risk_limited_test` record, or add a coercion lemma deriving it from the other fields.
13. Refactor `product_lr_Exp0_le1` so that `Omega`, `mu`, and `outcome` are section variables rather than universally quantified inside the lemma statement, making it usable as a direct plug-in for `rlt_ville`.
14. Weaken `ballot_prod_mu_sum1` to require only `0 < p` and `p < 1` instead of `2^{-1} < p`. Product-measure normalization does not depend on the null-hypothesis restriction.
15. Prove the algebraic simplification `k*alpha/(1-alpha) - k*alpha = k*alpha^2/(1-alpha)` and apply it in `exp_sandwich_gap` so the type matches the docstring.
16. Replace the vacuous `maricopa_macro_bound` (`x <= x`) with a concrete instantiation of `macro_uniform` at Maricopa parameters (k=265, alpha=5%).
17. Clean build artifacts from the working tree: `Makefile.coq`, `Makefile.coq.conf`, `.Makefile.coq.d`, `min_k.ml`, `min_k.mli`, `theories/.coq-native/*`, and all `.vo`/`.vos`/`.vok`/`.glob`/`.aux` files.
18. Set `install: [make "install" "DESTDIR=%{lib}%"]` (or equivalent) in `coq-auditing-verified.opam` so that `.vo` files are installed as a usable dependency.
19. Add a version pin for `coq-mathcomp-zify` in the opam file.
20. Consolidate `Q_scope` management in `concrete.v` into a single `Local Open Scope` or dedicated section.
21. Add proof-sketch comments to `tower_property` (ville.v) explaining the pair-sum flattening, swap bijection, and cell-mass cancellation steps.
22. Add deployment automation for the coqdoc GitHub Pages site, or remove the "latest build is published" claim from the README.
23. Fix the bibliography in `auditing.v`: `macro_false_assurance` (line 1384) does not exist as a lemma name; the actual lemmas are `macro_no_multiplicity`, `macro_uniform`, `macro_fa_le_hetero`, `macro_fa_strict_le_hetero`.
24. Add quantitative local sensitivity for conservative bounds: if `risks_j < alphas_j - epsilon`, bound the gap `F_hetero(alphas) - F_hetero(risks)` from below.
25. Prove the exponential sandwich is asymptotically tight as `alpha -> 0`.
26. Add a combined bivariate non-strict monotonicity lemma: `alpha1 <= alpha2 -> (k1 <= k2)%N -> F(alpha1,k1) <= F(alpha2,k2)`.
27. Add a `.coqdoc` options file controlling TOC, index generation, and CSS for `make doc`.
