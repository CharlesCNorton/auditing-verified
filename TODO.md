# Remaining gaps

1. Prove `QR_add` for cross-denominator arguments (requires an `int_of_Z` multiplication lemma). `QR_sub_same_denom` is done.
2. State and prove that the two-point distribution does NOT satisfy `events_independent` or `events_fully_independent`. `two_pt_product_gap` and `two_pt_dependence_gap` prove the numerical gap but never connect it to the probability-space independence definitions.
3. Prove `cond_exp` idempotency: `E[E[X|F_n] | F_n] = E[X|F_n]`.
4. Prove `frechet_lower_strict_general` for arbitrary `k` with a hypothesis `(2 <= k)%N` instead of requiring `k.+2`-indexed types.
5. Refactor `product_lr_Exp0_le1` so that `Omega`, `mu`, and `outcome` are section variables rather than universally quantified inside the lemma statement.
6. Bundle positive cell mass (`forall k x, 0 < \sum_(y | F k x y) mu y`) into the `filtration` record in `ville_6.v` and into `risk_limited_test` in `bravo_7.v`, eliminating the repeated `Hcell` threading in every consumer.
7. Prove surjectivity of the grouping from `complement_chromatic_le_styles` so that `overlap_hetero_pipeline` can fire without an external surjectivity proof.
8. Add a combined overlap pipeline lemma in `overlap_5.v` that takes only `covers`, `full_cov`, and `alphas` and directly produces the heterogeneous overlap bound.
9. Prove `search_k` is monotone in fuel: for any fuel above the minimum sufficient value, the output is the same.
10. Prove a general `min_k` correctness lemma: for all `alpha`, `delta` in (0,1) with sufficient fuel, `min_k` returns the least k such that `(1-alpha)^k <= 1-delta`.
11. Connect `concrete_hetero_3` to `false_assurance_hetero`: prove a lemma with `false_assurance_hetero` in its statement for three contests at 1%, 5%, 10% yielding false assurance at least 15%.
12. Prove cell-positivity for `ballot_F`: `forall k x, 0 < \sum_(y | ballot_F k x y) ballot_prod_mu y` from the structure of `ballot_prod_mu` and `ballot_F`.
13. Prove the coordinate-wise product factorization for sums over `{ffun 'I_N -> bool}` restricted to natural-filtration equivalence classes. This is the single hard lemma that unblocks items 14-18.
14. Prove `uniform_mu_sum1` and `uniform_marginal` for the uniform product measure on `{ffun 'I_k -> bool}`.
15. Instantiate `events_fully_independent` using the uniform product measure.
16. Prove the conditional independence of `lr(x_n)` given `ballot_F(n)` under the product measure.
17. Compose `ballot_plr_adapted` and `multiplicative_martingale_step` into the supermartingale inequality for `ballot_plr`: `E[ballot_plr(n+1) | F_n] <= ballot_plr(n)`. Then apply `ville_ineq` to get `Pr(ballot_plr >= 1/alpha) <= alpha` on the product space.
18. Instantiate `degradation_from_per_contest` with the product-space BRAVO bound from item 17 to obtain the joint false assurance bound end-to-end for k independent BRAVO tests.
19. Add a downstream proof that calls `partition_filtration`.
20. Add submartingale-specific results: upward Doob inequality, upward Ville analogue.
21. Prove the exponential sandwich is asymptotically tight as `alpha -> 0`.
22. Add quantitative local sensitivity for conservative bounds: if `risks_j < alphas_j - epsilon`, bound the gap `F_hetero(alphas) - F_hetero(risks)` from below.
23. Generalize the BRAVO model beyond binary ballots to multi-candidate contests.
24. Bridge the dependent model to a concrete dependent sampling construction (e.g., sampling without replacement across overlapping contests) and show it satisfies the model's preconditions.
25. Prove the algebraic simplification `k*alpha/(1-alpha) - k*alpha = k*alpha^2/(1-alpha)` and apply it in `exp_sandwich_gap` so the type matches the docstring.
