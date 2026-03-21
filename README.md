# Verified Multiplicative Degradation of Risk-Limiting Audits

A machine-checked formalization proving that per-contest assurance in
risk-limiting audits (RLAs) degrades multiplicatively with the number
of contests audited. When _k_ contests share a common risk limit _&alpha;_,
the probability of falsely certifying at least one incorrect outcome is
_1 &minus; (1 &minus; &alpha;)<sup>k</sup>_, which grows rapidly and exceeds any fixed
confidence threshold for sufficiently large _k_.

This result is well known in the election auditing literature (see, e.g.,
Stark, 2009; Lindeman and Stark, 2012), but to our knowledge this is the
first machine-checked formalization. The proofs are carried out over
MathComp's `realType` using MathComp Analysis for logarithms and real
exponentiation, with no axioms beyond the MathComp foundation.

## Proved results

The formalization establishes the following over an arbitrary real-closed
field `R`:

| Result | Statement |
|---|---|
| **Worst-case bound** | If each contest passes with probability at most _1 &minus; &alpha;_, the joint pass probability is at most _(1 &minus; &alpha;)<sup>k</sup>_, and false assurance is at least _1 &minus; (1 &minus; &alpha;)<sup>k</sup>_. |
| **Strict monotonicity** | False assurance is strictly increasing in _k_ for _&alpha; &isin; (0, 1)_. |
| **Threshold crossing** | For any _&alpha;, &delta; &isin; (0, 1)_, there exists _k<sub>0</sub>_ such that false assurance exceeds _&delta;_ for all _k &ge; k<sub>0</sub>_. Constructive via the Archimedean property. |
| **Logarithmic threshold** | _&delta; &le; 1 &minus; (1 &minus; &alpha;)<sup>k</sup>_ if and only if _k &ge; ln(1 &minus; &delta;) / ln(1 &minus; &alpha;)_. Both directions proved. |
| **Per-contest degradation** | If _&delta; &le; F(&alpha;, k)_, then each contest must satisfy _&alpha; &ge; 1 &minus; (1 &minus; &delta;)<sup>1/k</sup>_. Proved via _k_-th root extraction using `powR`. |
| **No fixed bound** | No single _k_ achieves all confidence levels: for every _k_, there exists _&delta;_ exceeding _F(&alpha;, k)_. |
| **Concrete validation** | For _&alpha; = 5%_ and _&delta; = 99%_: _(19/20)<sup>90</sup> &le; 1/100_ (verified by computation), and 89 contests do not suffice (sharpness). |

The independence model uses finite-indexed products (`&prod;_(i < k) p_i`
over `'I_k -> R`) to structurally enforce that the number of pass
probabilities matches the contest count.

## Practical significance

A jurisdiction running 90 or more contests at a 5% risk limit per contest
has less than 1% probability that all incorrect outcomes are caught.
The threshold formula _k<sub>0</sub> = &lceil;ln(1 &minus; &delta;) / ln(1 &minus; &alpha;)&rceil;_
gives the exact crossover point for any parameter choice, and the
per-contest degradation bound quantifies how much tighter each individual
risk limit must be to maintain a desired overall confidence level.

## Dependencies

- [Rocq](https://rocq-prover.org/) 9.0 (or Coq 8.20)
- [MathComp](https://math-comp.github.io/) &ge; 2.5
- [MathComp Analysis](https://github.com/math-comp/analysis) &ge; 1.15

## Building

```
make
```

This generates `Makefile.coq` via `rocq makefile` and compiles `auditing.v`.

With opam:

```
opam install coq-mathcomp-ssreflect coq-mathcomp-algebra coq-mathcomp-analysis
make
```

## File structure

- `auditing.v` &mdash; all definitions, lemmas, and proofs
- `coq-auditing-verified.opam` &mdash; opam package metadata
- `todo.md` &mdash; open problems and planned extensions

## References

- P. B. Stark. "Risk-limiting post-election audits: Conservative _P_-values
  from common probability inequalities." _IEEE Trans. Inform. Forensics
  Security_, 2009.
- M. Lindeman and P. B. Stark. "A gentle introduction to risk-limiting
  audits." _IEEE Security & Privacy_, 2012.

## License

MIT
