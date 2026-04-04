# Remaining gaps

1. **[BLOCKER]** Prove the coordinate-wise product factorization for sums over `{ffun 'I_N -> bool}` restricted to natural-filtration equivalence classes. Boundary cases (`n=0`, `n=N`) are done; the general case requires a restricted `bigA_distr_bigA` argument.
2. **[blocked by 1]** Prove `uniform_mu_sum1` and `uniform_marginal` for the uniform product measure on `{ffun 'I_k -> bool}`.
3. **[blocked by 2]** Instantiate `events_fully_independent` using the uniform product measure.
4. **[blocked by 3]** Prove the conditional independence of `lr(x_n)` given `ballot_F(n)` under the product measure.
5. **[blocked by 4]** Compose `ballot_plr_adapted` and `multiplicative_martingale_step` into the supermartingale inequality for `ballot_plr`: `E[ballot_plr(n+1) | F_n] <= ballot_plr(n)`. Then apply `ville_ineq` to get `Pr(ballot_plr >= 1/alpha) <= alpha` on the product space.
6. **[blocked by 5]** Instantiate `degradation_from_per_contest` with the product-space BRAVO bound to close the joint false assurance bound end-to-end for k independent BRAVO tests.
7. Generalize the BRAVO model beyond binary ballots to multi-candidate contests.
8. Add CI configuration (`.github/workflows/`).
