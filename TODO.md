# Remaining gaps

1. ~~**[BLOCKER]** Prove the coordinate-wise product factorization for sums over `{ffun 'I_N -> bool}` restricted to natural-filtration equivalence classes.~~ **DONE** (`ballot_F_cell_mass` proved).
2. ~~Prove `uniform_mu_sum1` and `uniform_marginal` for the uniform product measure on `{ffun 'I_k -> bool}`.~~ **Superseded**: `ballot_F_cell_mass_coord` provides the per-coordinate factorization needed by item 4 directly; separate marginal/independence lemmas are not required for the pipeline.
3. ~~Instantiate `events_fully_independent` using the uniform product measure.~~ **Superseded**: full subset independence is not needed; item 4 provides the conditional independence that feeds item 5 directly.
4. ~~**[blocked by 1]** Prove the conditional independence of `lr(x_n)` given `ballot_F(n)` under the product measure.~~ **DONE** (`ballot_F_cond_exp_lr` proves `E[lr(f_n) | F_n] = 1`).
5. **[blocked by 4, in progress]** Compose `ballot_plr_adapted` and `multiplicative_martingale_step` into the supermartingale inequality for `ballot_plr`: `E[ballot_plr(n+1) | F_n] <= ballot_plr(n)`. Then apply `ville_ineq` to get `Pr(ballot_plr >= 1/alpha) <= alpha` on the product space. Requires defining a time-varying process indexed by step `n` (first `n` coordinates) and connecting the ordinal coercions between `'I_n` and `'I_N`.
6. **[blocked by 5]** Instantiate `degradation_from_per_contest` with the product-space BRAVO bound to close the joint false assurance bound end-to-end for k independent BRAVO tests.
7. **[future extension]** Generalize the BRAVO model beyond binary ballots to multi-candidate contests.
8. ~~Add CI configuration (`.github/workflows/`).~~ **DONE**.
