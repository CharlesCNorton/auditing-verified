# Remaining gaps

1. Fix the bibliography in `auditing_1.v`: `macro_false_assurance` does not exist as a lemma name; the actual lemmas are `macro_no_multiplicity`, `macro_uniform`, `macro_fa_le_hetero`, `macro_fa_strict_le_hetero`.
2. Factor `sum_divr` out of its two inline copies in `optimal_2.v` (lines 69-73 and 184-188) into a single shared lemma.
3. Consolidate `Q_scope` management in `concrete_9.v` into a single `Local Open Scope` or dedicated section.
4. Add a version pin for `coq-mathcomp-zify` in the opam file.
5. Set `install: [make "install"]` in `coq-auditing-verified.opam` so that `.vo` files are installed as a usable dependency.
6. Remove or qualify the "latest build is published" claim in the README until deployment automation exists.
7. Add a `.coqdoc` options file controlling TOC, index generation, and CSS for `make doc`.
8. Add proof-sketch comments to `tower_property` (ville_6.v) explaining the pair-sum flattening, swap bijection, and cell-mass cancellation steps.
9. Weaken `ballot_prod_mu_sum1` to require only `0 < p` and `p < 1` instead of `2^{-1} < p`. Product-measure normalization does not depend on the null-hypothesis restriction.
10. Prove the algebraic simplification `k*alpha/(1-alpha) - k*alpha = k*alpha^2/(1-alpha)` and apply it in `exp_sandwich_gap` so the type matches the docstring.
11. Replace the vacuous `maricopa_macro_bound` (`x <= x`) with a concrete instantiation of `macro_uniform` at Maricopa parameters (k=265, alpha=5%).
12. Bundle `Hcell` (positive cell mass) into the `risk_limited_test` record, or add a coercion lemma deriving it from the other fields.
13. Refactor `product_lr_Exp0_le1` so that `Omega`, `mu`, and `outcome` are section variables rather than universally quantified inside the lemma statement, making it usable as a direct plug-in for `rlt_ville`.
14. Prove `QR_add` for cross-denominator arguments.
15. Add a combined bivariate non-strict monotonicity lemma: `alpha1 <= alpha2 -> (k1 <= k2)%N -> F(alpha1,k1) <= F(alpha2,k2)`.
16. Prove the coordinate-wise product factorization for sums over `{ffun 'I_N -> bool}` restricted to natural-filtration equivalence classes. This is the single hard lemma that unblocks items 17-22.
17. Prove `uniform_mu_sum1` and `uniform_marginal` for the uniform product measure on `{ffun 'I_k -> bool}`.
18. Instantiate `events_fully_independent` using the uniform product measure.
19. Prove the conditional independence of `lr(x_n)` given `ballot_F(n)` under the product measure.
20. Compose `ballot_plr_adapted` and `multiplicative_martingale_step` into the supermartingale inequality for `ballot_plr`: `E[ballot_plr(n+1) | F_n] <= ballot_plr(n)`.
21. State and prove that the two-point distribution does NOT satisfy `events_independent` or `events_fully_independent`. `two_pt_product_gap` and `two_pt_dependence_gap` prove the numerical gap but never connect it to the probability-space independence definitions.
22. Add a downstream proof that calls `partition_filtration`.
23. Prove `cond_exp` idempotency: `E[E[X|F_n] | F_n] = E[X|F_n]`. `cond_exp_measurable` handles adapted functions but general idempotency is absent.
24. Prove surjectivity of the grouping from `complement_chromatic_le_styles` so that `overlap_hetero_pipeline` can fire from the grouping alone without an external surjectivity proof.
25. Prove a general `min_k` correctness lemma linking `search_k` output to `(1-alpha)^k <= 1-delta` for arbitrary inputs.
26. Add submartingale-specific results: upward Doob inequality, upward Ville analogue. Currently only the definition and coercion from martingale exist.
27. Prove the exponential sandwich is asymptotically tight as `alpha -> 0`.
28. Add quantitative local sensitivity for conservative bounds: if `risks_j < alphas_j - epsilon`, bound the gap `F_hetero(alphas) - F_hetero(risks)` from below.
