# Remaining gaps

1. **[in progress]** Compose `ballot_plr_adapted` and `multiplicative_martingale_step` into the supermartingale inequality for `ballot_plr`: `E[ballot_plr(n+1) | F_n] <= ballot_plr(n)`. Then apply `ville_ineq` to get `Pr(ballot_plr >= 1/alpha) <= alpha` on the product space. Requires defining a time-varying process indexed by step `n` (first `n` coordinates) and connecting the ordinal coercions between `'I_n` and `'I_N`.
2. **[blocked by 1]** Instantiate `degradation_from_per_contest` with the product-space BRAVO bound to close the joint false assurance bound end-to-end for k independent BRAVO tests.
3. **[future extension]** Generalize the BRAVO model beyond binary ballots to multi-candidate contests.
