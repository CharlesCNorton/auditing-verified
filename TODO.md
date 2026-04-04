# Remaining gaps

1. ~~**[BLOCKER]** Prove the coordinate-wise product factorization for sums over `{ffun 'I_N -> bool}` restricted to natural-filtration equivalence classes.~~ **DONE** (`ballot_F_cell_mass`).
2. ~~Prove `uniform_mu_sum1` and `uniform_marginal` for the uniform product measure.~~ **Superseded**: `ballot_F_cell_mass_coord` provides the per-coordinate factorization directly.
3. ~~Instantiate `events_fully_independent` using the uniform product measure.~~ **Superseded**: full subset independence is not needed; `ballot_F_cond_exp_lr` provides the conditional independence that feeds item 5 directly.
4. ~~Prove the conditional independence of `lr(x_n)` given `ballot_F(n)` under the product measure.~~ **DONE** (`ballot_F_cond_exp_free`, `ballot_F_cond_exp_lr`).
5. ~~Compose into the supermartingale inequality for `ballot_plr` and apply `ville_ineq`.~~ **DONE** (`bravo_ville`). The current proof uses the time-constant indexing (`ballot_plr` at the full horizon `N`); a time-varying formulation with ordinal coercions between `'I_n` and `'I_N` at each step would give a tighter per-step bound but is not needed for the degradation connection.
6. ~~Instantiate `degradation_from_per_contest` with the BRAVO bound.~~ **DONE** (`bravo_degradation`).
7. **[future extension]** Generalize the BRAVO model beyond binary ballots to multi-candidate contests.
8. ~~Add CI configuration.~~ **DONE** (`.github/workflows/ci.yml`).
