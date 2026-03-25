# Remaining gaps

All items compile-tested against Rocq 9.0 / MathComp 2.5 / MathComp Analysis 1.15. Zero Admitted.

1. Prove the conditional independence of `lr(x_n)` given `ballot_F(n)` under the product measure.
2. Prove `QR_add` for cross-denominator arguments.
3. Prove `uniform_mu_sum1` and `uniform_marginal` for the uniform product measure on `{ffun 'I_k -> bool}`.
4. Instantiate `events_fully_independent` using the uniform product measure.
5. Prove a general `min_k` correctness lemma linking `search_k` output to `(1-alpha)^k <= 1-delta` for arbitrary inputs.
6. Add a downstream proof that calls `partition_filtration`.

Items 1, 3, 4, 6 all converge on one technical kernel: decomposing sums over `{ffun 'I_N -> bool}` into coordinate-wise products when restricted to equivalence classes of the natural filtration. Once that factorization lemma exists, all four close immediately.
