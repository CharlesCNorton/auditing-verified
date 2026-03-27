# Verified Multiplicative Degradation of Risk-Limiting Audits

A machine-checked formalization proving that per-contest assurance in
risk-limiting audits (RLAs) degrades multiplicatively with the number
of contests audited. When _k_ contests share a common risk limit _&alpha;_,
the probability of falsely certifying at least one incorrect outcome is
_1 &minus; (1 &minus; &alpha;)<sup>k</sup>_, which grows rapidly and exceeds any fixed
confidence threshold for sufficiently large _k_.

The underlying correction _1 &minus; (1 &minus; &alpha;)<sup>k</sup>_ is the
&Scaron;id&aacute;k correction (&Scaron;id&aacute;k, 1967), long standard in
multiple-testing theory and applied to election auditing by Stark (2009)
and Lindeman and Stark (2012). To our knowledge this is the first
machine-checked formalization of the &Scaron;id&aacute;k correction in
the election auditing context, and the first mechanized proof of
discrete (finite-state) Ville's inequality in any proof assistant (see
[Related formalizations](#related-formalizations) below for a comparison
with Lean/Mathlib and Isabelle/HOL martingale work). The formalization
operates over finite sample spaces (`finType`), which eliminates the
integrability conditions and null-set subtleties present in the
measure-theoretic version. Priority claims are based on a survey of
Lean/Mathlib, the Isabelle AFP, and the Coq/Rocq opam registry as of
March 2026.

The proofs are carried out over MathComp's `realType` using MathComp
Analysis for logarithms and real exponentiation, with no axioms beyond
the MathComp foundation and no admitted proofs.

## Proved results

### Algebraic degradation theory

The formalization establishes the following over an arbitrary real-closed
field `R`:

| Result | Statement |
|---|---|
| **Worst-case bound** | If each contest passes with probability at most _1 &minus; &alpha;_, the joint pass probability is at most _(1 &minus; &alpha;)<sup>k</sup>_, and false assurance is at least _1 &minus; (1 &minus; &alpha;)<sup>k</sup>_. |
| **Equality uniqueness** | The worst-case bound is tight only when every contest has pass probability exactly _1 &minus; &alpha;_. The uniform distribution is the unique extremal. |
| **Strict monotonicity** | False assurance is strictly increasing in _k_ for _&alpha; &isin; (0, 1)_, and non-decreasing in _&alpha;_ for fixed _k_. Bivariate strict monotonicity when either parameter increases. |
| **Union bound** | _F(&alpha;, k) &le; k&alpha;_, the classical Boole bound. Strict for _k &ge; 2_. |
| **Exponential sandwich** | _1 &minus; exp(&minus;k&alpha;) &le; F(&alpha;, k) &le; 1 &minus; exp(&minus;k&alpha;/(1&minus;&alpha;))_. Both bounds proved with explicit gap control. |
| **Threshold crossing** | For any _&alpha;, &delta; &isin; (0, 1)_, there exists _k<sub>0</sub>_ such that false assurance exceeds _&delta;_ for all _k &ge; k<sub>0</sub>_. Constructive via the Archimedean property, with the witness _k<sub>0</sub> = archi\_bound(ln(1&minus;&delta;)/ln(1&minus;&alpha;))_ exposed in the type. |
| **Logarithmic threshold** | _&delta; &le; 1 &minus; (1 &minus; &alpha;)<sup>k</sup>_ if and only if _k &ge; ln(1 &minus; &delta;) / ln(1 &minus; &alpha;)_. Both directions proved. |
| **Per-contest degradation** | If _&delta; &le; F(&alpha;, k)_, then _&alpha; &ge; 1 &minus; (1 &minus; &delta;)<sup>1/k</sup>_. Proved via _k_-th root extraction using `powR`. |
| **k-Lipschitz sensitivity** | _F(&alpha;<sub>2</sub>, k) &minus; F(&alpha;<sub>1</sub>, k) &le; k(&alpha;<sub>2</sub> &minus; &alpha;<sub>1</sub>)_ for _&alpha;<sub>1</sub> &le; &alpha;<sub>2</sub>_. |
| **Heterogeneous risk limits** | For per-contest risk limits _&alpha;<sub>i</sub>_, false assurance _1 &minus; &prod;(1 &minus; &alpha;<sub>i</sub>)_ is monotone in each _&alpha;<sub>i</sub>_, bounded in [0, 1], satisfies the union bound _F &le; &sum;&alpha;<sub>i</sub>_, and is sandwiched by exponential bounds. Reduces to the uniform case when all _&alpha;<sub>i</sub>_ are equal. |
| **AM-GM optimal allocation** | Uniform allocation minimizes false assurance for a given total risk budget. Strict optimality: any non-uniform split yields strictly higher false assurance. The uniform allocation is the unique minimizer. |
| **Dependent audit model** | Under arbitrary dependence, the joint pass probability satisfies Fr&eacute;chet bounds. Positive dependence reduces false assurance below the independence baseline; negative dependence worsens it. The dependence gap _F<sub>dep</sub> &minus; F<sub>indep</sub> = &prod;(1&minus;&alpha;<sub>i</sub>) &minus; p<sub>joint</sub>_ classifies the regime. |
| **MACRO model** | All-or-nothing escalation eliminates the multiplicity problem: false assurance equals the minimum individual risk limit, bounded by each _&alpha;<sub>j</sub>_ regardless of _k_. |
| **Conservative risk limits** | When actual risks fall below their limits, the nominal bound overestimates. Equality holds only when every contest achieves its limit exactly. |
| **Ballot overlap** | Contests sharing ballot styles reduce the effective degradation parameter from _k_ (contests) to _n_ (ballot styles). Heterogeneous overlap bound via injective witness. Complement coloring: contests sharing a ballot style are grouped together, bounding the effective number of independent groups by _n_. |
| **Sequential/anytime audits** | The degradation bound is mechanism-agnostic: it holds at any collection of stopping times, assuming per-contest bounds hold at each time step (the interface to Ville's inequality). |
| **Continuity** | False assurance is continuous in _&alpha;_ and separately continuous in each heterogeneous coordinate. The coordinate slice is affine, hence C-infinity. |

### False certification rate

| Result | Statement |
|---|---|
| **FCR first bound** | _FCR &le; (&sum;&alpha;<sub>i</sub>) / (k &minus; m)_, where _m_ is the number of wrong contests. |
| **FWER &ge; FCR** | The family-wise error rate (probability any wrong outcome survives) bounds the false certification rate from above. Proved by `big_rec2` induction on the cross-multiplied form _(c + V) &middot; P &le; c_. |

### Finite probability space

| Result | Statement |
|---|---|
| **Pr axioms** | Non-negativity, normalization, complementation, monotonicity on a finite probability space (`finType` with non-negative weights summing to 1). |
| **Subadditivity** | _Pr(A &cup; B) &le; Pr(A) + Pr(B)_. Proved via `bigID` decomposition into disjoint parts. |
| **Independence &rarr; product** | Under statistical independence (full-intersection form), `joint_pass(Pr(E_i)) = Pr(&cap; E_i)`. Formally connects the algebraic product model to the probabilistic model. |
| **Worst-case transfer** | Under independence with per-contest risk bounds, the algebraic false assurance bound transfers to the probability model. |

### Two-point distribution

| Result | Statement |
|---|---|
| **Normalization** | The two-point distribution on `{ffun 'I_k &rarr; bool}` (mass _1 &minus; t_ on all-pass, mass _t_ on all-fail) sums to 1. Proved via `bigD1` extraction. |
| **Marginals** | Each contest's pass probability equals _1 &minus; t_ under the two-point distribution. |
| **False assurance** | _1 &minus; Pr(all pass) = t_ exactly. Realizes the Fr&eacute;chet-Hoeffding extremal under maximal positive correlation. |

### Discrete supermartingale theory

| Result | Statement |
|---|---|
| **Conditional expectation** | Defined as the cell-weighted average on a finite equivalence-relation filtration. Measurable functions are fixed points. |
| **Tower property** | _E[E[X &mid; F<sub>n</sub>]] = E[X]_. Proved by `pair_big_dep` flattening to pair sums, `equiv_class_sum` for cell-mass cancellation, and `reindex_inj` with the pair-swap bijection. |
| **Supermartingale monotonicity** | _E[M<sub>n+1</sub>] &le; E[M<sub>n</sub>]_ from the tower property and the supermartingale inequality. |
| **Iterated monotonicity** | _E[M<sub>n</sub>] &le; E[M<sub>0</sub>]_ for all _n_, by induction. |
| **Markov's inequality** | _c &middot; Pr(X &ge; c) &le; E[X]_ for non-negative _X_ and _c > 0_. |
| **Ville's inequality** | For a non-negative supermartingale with _E[M<sub>0</sub>] &le; 1_: _Pr(M<sub>n</sub> &ge; 1/&alpha;) &le; &alpha;_. Combines iterated monotonicity with Markov. |
| **Optional stopping theorem** | For a bounded stopping time &tau; &le; N: _E[M<sub>&tau;</sub>] &le; E[M<sub>0</sub>]_. The stopped process is shown to be a supermartingale via case analysis on &tau;(x) &le; n. |
| **Ville at stopping times** | _Pr(M<sub>&tau;</sub> &ge; 1/&alpha;) &le; &alpha;_ for any bounded stopping time. Combines optional stopping with Markov. |
| **Doob's maximal inequality** | _c &middot; Pr(M<sub>&tau;</sub> &ge; c) &le; E[M<sub>0</sub>]_ for any bounded stopping time and _c > 0_. |
| **Martingale/submartingale** | Definitions for equality and reversed-inequality variants. Coercion lemmas to supermartingale. |
| **Filtration-partition equivalence** | Equivalence classes of a filtration form a partition (cover, disjointness, non-emptiness). Partition-derived equivalence is reflexive, symmetric, transitive. Roundtrip: `partition_equiv (equiv_classes E) = E`. Filtration refinement implies partition refinement. |

### Concrete validation

| Result | Statement |
|---|---|
| **Concrete bound** | _(19/20)<sup>90</sup> &le; 1/100_ verified by `vm_compute` in Stdlib Q, transferred to `realType` via the `QR` bridge. |
| **Sharpness** | 89 contests do not suffice. Both directions proved. Extended to all _k &ge; 90_ via monotonicity. |
| **Heterogeneous concrete** | Three contests at 1%, 5%, 10% yield false assurance at least 15%. |
| **Maricopa County 2024** | For Maricopa County's 265 contests at _&alpha; = 5%_: false assurance exceeds 99.99%. With 80 independent groups: exceeds 98.3%. Under MACRO: capped at 5%. |
| **Extraction target** | Computable function `min_k` in Stdlib Q returns the minimum _k_ for given _&alpha;_ and _&delta;_. Verified: `min_k(1/20, 99/100) = 90`. |

## Practical significance

Under the worst-case model&mdash;every reported outcome is wrong, contests
are audited with independent samples, and each contest achieves exactly
its risk limit&mdash;a jurisdiction running 90 or more contests at a 5%
risk limit per contest has less than 1% probability that all incorrect
outcomes are caught. The threshold formula
_k<sub>0</sub> = &lceil;ln(1 &minus; &delta;) / ln(1 &minus; &alpha;)&rceil;_
gives the exact crossover point for any parameter choice, and the
per-contest degradation bound quantifies how much tighter each individual
risk limit must be to maintain a desired overall confidence level.

For Maricopa County's 265 contests (2024 General Election), the
formalization verifies that false assurance under independence exceeds
99.99% at a 5% per-contest risk limit. Grouping contests into 80
ballot-style-based groups reduces false assurance to 98.3%. Only
all-or-nothing methods like MACRO, which trigger a full hand count when
any single contest escalates, eliminate the multiplicity problem entirely.

The supermartingale foundation (Ville's inequality) ensures these bounds
hold for any sequential audit method&mdash;including BRAVO, ALPHA, and
other martingale-based tests&mdash;at any data-dependent stopping time,
not just fixed sample sizes. The per-contest risk bound is justified by
the supermartingale's expectation monotonicity and Markov's inequality,
giving a complete probabilistic chain from test construction to
degradation conclusion.

## Axiom footprint

Every theorem in the formalization depends only on the three standard
MathComp classical axioms:

- `propositional_extensionality`
- `functional_extensionality_dep`
- `constructive_indefinite_description`

No proofs are admitted. The axiom audit is included at the end of
`auditing_1.v` via `Print Assumptions` for all key results.

## Building

```
make
```

This generates `Makefile.coq` via `rocq makefile` and compiles
all source files in `theories/`.

To generate HTML documentation:

```
make doc
```

This produces browsable coqdoc output in `html/`. A snapshot is hosted at https://charlescnorton.github.io/auditing-verified/ (may lag behind the latest source).

## Dependencies

- [Rocq](https://rocq-prover.org/) 9.0
- [MathComp](https://math-comp.github.io/) &ge; 2.5
- [MathComp Analysis](https://github.com/math-comp/analysis) &ge; 1.15
- [MathComp Zify](https://github.com/math-comp/mczify) (for the Q-to-R bridge)

With opam:

```
opam install coq-mathcomp-ssreflect coq-mathcomp-algebra coq-mathcomp-analysis coq-mathcomp-zify
make
```

## Documentation

Browsable coqdoc output: https://charlescnorton.github.io/auditing-verified/

## File structure

| File | Lines | Contents |
|------|------:|----------|
| `auditing_1.v` | ~1430 | Core definitions, algebraic degradation theory, heterogeneous risk limits, FCR/FWER, shared/simultaneous audits, conservative bounds |
| `optimal_2.v` | ~250 | AM-GM inequality, optimal risk allocation, strict optimality, unique minimizer |
| `dependent_3.v` | ~440 | Dependent audit model, Fr&eacute;chet bounds, Weierstrass product inequality, MACRO model, negative dependence witnesses |
| `probability_4.v` | ~350 | Finite probability space (Pr axioms, subadditivity, independence), two-point distribution, Fr&eacute;chet-Hoeffding extremal |
| `overlap_5.v` | ~260 | Ballot overlap bounds, chromatic number, heterogeneous overlap, complement coloring |
| `ville_6.v` | ~770 | Discrete supermartingale theory, tower property, Ville's inequality, optional stopping, Doob's maximal inequality, filtration-partition equivalence |
| `bravo_7.v` | ~585 | BRAVO ballot-polling audit, likelihood ratio martingale, product-space measure, degradation connection, multiplicative martingale step |
| `continuity_8.v` | ~80 | Continuity and differentiability of false assurance (MathComp Analysis topology scope isolation) |
| `concrete_9.v` | ~415 | Concrete validation in Stdlib Q, Maricopa County 2024 instantiation, Q-to-R transfer via QR injection, min_k extraction target |

- `coq-auditing-verified.opam` &mdash; opam package metadata

**Domain aliases.** `overlap_5.v` and `dependent_3.v` re-export several
core results from `auditing_1.v` under domain-specific names (e.g.
`overlap_bound` wraps `false_assurance_mono`, `macro_fa_le_hetero`
wraps `independence_worsens_assurance`).  These aliases improve
readability in the election-auditing context without adding new
mathematical content.

## Related formalizations

The probability and martingale theory formalized here sits in a broader
landscape of machine-checked probability:

- **Lean / Mathlib.** Conditional expectation, filtrations, martingales,
  submartingales, and the martingale convergence theorem have been
  formalized by Kexing Ying and R&eacute;my Degenne.
  See K. Ying and R. Degenne, &ldquo;A formalization of Doob's
  martingale convergence theorems in mathlib,&rdquo; _CPP 2022_,
  pp. 132&ndash;145.
  [DOI: 10.1145/3497775.3503559](https://doi.org/10.1145/3497775.3503559).
  Mathlib does not contain Ville's inequality.

- **Isabelle / HOL.** Measure theory and probability by Johannes
  H&ouml;lzl (TU M&uuml;nchen). The AFP entry &ldquo;Martingales&rdquo;
  by Ata Keskin (2024) formalizes martingales, Doob's upcrossing
  inequality, and the martingale convergence theorem.

- **Coq / MathComp Analysis.** Measure theory and Lebesgue integration
  by Reynald Affeldt, Cyril Cohen, et al.
  See R. Affeldt et al., &ldquo;Measure construction by extension in
  dependent type theory with application to integration,&rdquo;
  _J. Automated Reasoning_, 67, Article 12, 2023.
  [DOI: 10.1007/s10817-023-09671-5](https://doi.org/10.1007/s10817-023-09671-5).
  MathComp Analysis does not contain martingale theory.

To our knowledge, no proof assistant contains a formalization of
discrete Ville's inequality, the &Scaron;id&aacute;k correction, or
risk-limiting audit theory prior to this work.

## References

### Election auditing

- Z. &Scaron;id&aacute;k. &ldquo;Rectangular confidence regions for the
  means of multivariate normal distributions.&rdquo;
  _J. Amer. Statist. Assoc._, 62(318):626&ndash;633, 1967.
  [DOI: 10.1080/01621459.1967.10482935](https://doi.org/10.1080/01621459.1967.10482935)
- P. B. Stark. &ldquo;Conservative statistical post-election
  audits.&rdquo; _Ann. Appl. Stat._, 2(2):550&ndash;581, 2008.
  [DOI: 10.1214/08-AOAS161](https://doi.org/10.1214/08-AOAS161)
- P. B. Stark. &ldquo;Risk-limiting postelection audits: Conservative
  _P_-values from common probability inequalities.&rdquo; _IEEE Trans.
  Inform. Forensics Security_, 4(4):1005&ndash;1014, 2009.
  [DOI: 10.1109/TIFS.2009.2034190](https://doi.org/10.1109/TIFS.2009.2034190)
- P. B. Stark. &ldquo;Efficient post-election audits of multiple
  contests: 2009 California tests.&rdquo; SSRN, 2009.
  [DOI: 10.2139/ssrn.1443314](https://doi.org/10.2139/ssrn.1443314)
- M. Lindeman and P. B. Stark. &ldquo;A gentle introduction to
  risk-limiting audits.&rdquo; _IEEE Security &amp; Privacy_,
  10(5):42&ndash;49, 2012.
  [DOI: 10.1109/MSP.2012.56](https://doi.org/10.1109/MSP.2012.56)
- M. Lindeman, P. B. Stark, and V. S. Yates. &ldquo;BRAVO:
  Ballot-polling risk-limiting audits to verify outcomes.&rdquo;
  _2012 Electronic Voting Technology Workshop / Workshop on
  Trustworthy Elections (EVT/WOTE &rsquo;12)_, USENIX, 2012.
- P. B. Stark. &ldquo;Sets of half-average nulls generate
  risk-limiting audits: SHANGRLA.&rdquo; In _Financial Cryptography
  and Data Security: FC 2020 International Workshops_, LNCS 12063,
  pp. 319&ndash;336, Springer, 2020.
  [DOI: 10.1007/978-3-030-54455-3_23](https://doi.org/10.1007/978-3-030-54455-3_23)
- P. B. Stark. &ldquo;ALPHA: Audit that learns from previously
  hand-audited ballots.&rdquo; _Ann. Appl. Stat._,
  17(1):641&ndash;679, 2023.
  [DOI: 10.1214/22-AOAS1646](https://doi.org/10.1214/22-AOAS1646)
- Maricopa County Elections Department. &ldquo;2024 General Election
  Information Now Available Online.&rdquo; elections.maricopa.gov,
  October 2024.

### Probability and inequalities

- A. N. Kolmogorov. _Grundbegriffe der Wahrscheinlichkeitsrechnung._
  Ergebnisse der Mathematik, Springer, Berlin, 1933. English
  translation: _Foundations of the Theory of Probability_, Chelsea,
  New York, 1950.
- J. Ville. _&Eacute;tude critique de la notion de collectif._
  Gauthier-Villars, Paris, 1939.
- J. L. Doob. _Stochastic Processes._ John Wiley &amp; Sons,
  New York, 1953. ISBN: 978-0-471-52369-7.
- M. Fr&eacute;chet. &ldquo;G&eacute;n&eacute;ralisation du
  th&eacute;or&egrave;me des probabilit&eacute;s totales.&rdquo;
  _Fundamenta Mathematicae_, 25:379&ndash;387, 1935.
  [DOI: 10.4064/fm-25-1-379-387](https://doi.org/10.4064/fm-25-1-379-387)
- P. L. Chebyshev. &ldquo;Des valeurs moyennes.&rdquo; _J. Math.
  Pures Appl._, 2e s&eacute;rie, 12:177&ndash;184, 1867.
- G. Boole. _An Investigation of the Laws of Thought, on Which Are
  Founded the Mathematical Theories of Logic and Probabilities._
  Walton and Maberly, London, 1854.
  [DOI: 10.1017/CBO9780511693090](https://doi.org/10.1017/CBO9780511693090)
  (Cambridge reprint)
- A.-L. Cauchy. _Cours d'analyse de l'&Eacute;cole Royale
  Polytechnique. Premi&egrave;re partie: Analyse
  alg&eacute;brique._ L'Imprimerie Royale, Paris, 1821.
- G. H. Hardy, J. E. Littlewood, and G. P&oacute;lya.
  _Inequalities._ 2nd ed., Cambridge University Press, 1952.
- D. S. Mitrinovi&cacute;. _Analytic Inequalities._ Grundlehren der
  mathematischen Wissenschaften, Springer-Verlag, 1970.
  [DOI: 10.1007/978-3-642-99970-3](https://doi.org/10.1007/978-3-642-99970-3)

A per-lemma bibliography with DOIs is included at the end of
`auditing_1.v`, `ville_6.v`, `bravo_7.v`, `dependent_3.v`, and `optimal_2.v`.

## License

MIT
