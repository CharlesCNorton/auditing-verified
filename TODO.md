# Remaining gaps

1. Prove cell-positivity for `ballot_F`: `forall k x, 0 < \sum_(y | ballot_F k x y) ballot_prod_mu y` from the structure of `ballot_prod_mu` and `ballot_F`.
2. Prove the coordinate-wise product factorization for sums over `{ffun 'I_N -> bool}` restricted to natural-filtration equivalence classes. This is the single hard lemma that unblocks items 3-7.
3. Prove `uniform_mu_sum1` and `uniform_marginal` for the uniform product measure on `{ffun 'I_k -> bool}`.
4. Instantiate `events_fully_independent` using the uniform product measure.
5. Prove the conditional independence of `lr(x_n)` given `ballot_F(n)` under the product measure.
6. Compose `ballot_plr_adapted` and `multiplicative_martingale_step` into the supermartingale inequality for `ballot_plr`: `E[ballot_plr(n+1) | F_n] <= ballot_plr(n)`. Then apply `ville_ineq` to get `Pr(ballot_plr >= 1/alpha) <= alpha` on the product space.
7. Instantiate `degradation_from_per_contest` with the product-space BRAVO bound from item 6 to obtain the joint false assurance bound end-to-end for k independent BRAVO tests.
8. Add a downstream proof that calls `partition_filtration`.
9. Add submartingale-specific results: upward Doob inequality, upward Ville analogue.
10. Prove the exponential sandwich is asymptotically tight as `alpha -> 0`.
11. Add quantitative local sensitivity for conservative bounds: if `risks_j < alphas_j - epsilon`, bound the gap `F_hetero(alphas) - F_hetero(risks)` from below.
12. Generalize the BRAVO model beyond binary ballots to multi-candidate contests.
13. Bridge the dependent model to a concrete dependent sampling construction (e.g., sampling without replacement across overlapping contests) and show it satisfies the model's preconditions.
14. Prove the algebraic simplification `k*alpha/(1-alpha) - k*alpha = k*alpha^2/(1-alpha)` and apply it in `exp_sandwich_gap` so the type matches the docstring.
