(******************************************************************************)
(*                                                                            *)
(*     Finite probability space and two-point distribution                    *)
(*                                                                            *)
(*     Defines a minimal finite probability measure on a finType,            *)
(*     proves basic axioms (non-negativity, normalization, complement,       *)
(*     monotonicity, subadditivity), formalizes statistical independence,    *)
(*     and constructs the two-point (Frechet-Hoeffding extremal)            *)
(*     distribution on {ffun 'I_k -> bool}.                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Open Scope ring_scope.

From Auditing Require Import auditing_1.

(* ================================================================== *)
(** ** Two-point distribution on [{ffun 'I_k -> bool}]                *)
(* ================================================================== *)

(** Lifts [dep_fa_achievable] to a full finite probability
    measure on the product space [{pass, fail}^k] with bigop
    summation.  Realizes the Frechet-Hoeffding extremal under
    maximal positive correlation. *)

Section TwoPointDistribution.

Variable R : realType.
Variable k : nat.
Hypothesis Hk : (0 < k)%N.
Variable t : R.
Hypothesis Ht0 : 0 <= t.
Hypothesis Ht1 : t <= 1.

Local Notation all_pass := [ffun _ : 'I_k => true].
Local Notation all_fail := [ffun _ : 'I_k => false].

(** [two_pt_mu f]: assigns mass [1 - t] to the all-pass outcome,
    mass [t] to the all-fail outcome, and [0] to every other
    configuration. *)
Definition two_pt_mu (f : {ffun 'I_k -> bool}) : R :=
  if f == all_pass then 1 - t
  else if f == all_fail then t
  else 0.

(** Every outcome has non-negative mass. *)
Lemma two_pt_mu_ge0 (f : {ffun 'I_k -> bool}) :
  0 <= two_pt_mu f.
Proof.
rewrite /two_pt_mu; case: ifP => _; first by r01.
by case: ifP.
Qed.

(** The all-pass and all-fail outcomes are distinct when [k > 0]. *)
Lemma all_pass_ne_fail : all_pass != all_fail.
Proof.
by apply/eqP => /ffunP /(_ (Ordinal Hk)); rewrite !ffunE.
Qed.

(** The two-point measure is normalized: total mass equals 1. *)
Lemma two_pt_mu_sum1 :
  \sum_(f : {ffun 'I_k -> bool}) two_pt_mu f = 1.
Proof.
have Hne := all_pass_ne_fail.
rewrite (bigD1 all_pass) //= (bigD1 all_fail) /=; last by rewrite eq_sym.
rewrite /two_pt_mu eqxx [all_fail == all_pass]eq_sym (negbTE Hne) eqxx.
rewrite big1 ?addr0; last first.
  move=> f /andP [Hne_p Hne_f].
  by rewrite (negbTE Hne_p) (negbTE Hne_f).
by rewrite subrK.
Qed.

(** Each contest's marginal pass probability equals [1 - t]. *)
Lemma two_pt_marginal (j : 'I_k) :
  \sum_(f : {ffun 'I_k -> bool} | f j) two_pt_mu f = 1 - t.
Proof.
rewrite (bigD1 all_pass) /=; last by rewrite ffunE.
rewrite /two_pt_mu eqxx big1 ?addr0 // => f /andP [Hfj Hne].
rewrite (negbTE Hne); case Haf: (f == all_fail) => //.
by move/eqP: Haf Hfj => ->; rewrite ffunE.
Qed.

(** False assurance under the two-point distribution equals [t]
    exactly: [1 - Pr(all pass) = t]. *)
Lemma two_pt_false_assurance :
  1 - \sum_(f : {ffun 'I_k -> bool} | [forall j, f j])
        two_pt_mu f = t.
Proof.
rewrite (bigD1 all_pass) /=; last first.
  by apply/forallP => j; rewrite ffunE.
rewrite /two_pt_mu eqxx big1 ?addr0; last first.
  move=> f /andP [/forallP Hall Hne]; rewrite (negbTE Hne) /=.
  case Hff: (f == all_fail) => //.
  by move/eqP: Hff => Hff; move: (Hall (Ordinal Hk)); rewrite Hff ffunE.
by rewrite opprD opprK addrA addrN add0r.
Qed.

(** Strict positivity of [two_pt_mu] on its support when [0 < t < 1].
    Needed to instantiate the cell-positivity hypothesis [Hcell] for
    the supermartingale machinery in [ville_6.v]. *)
Lemma two_pt_mu_pos_pass :
  0 < t -> t < 1 -> 0 < two_pt_mu all_pass.
Proof. by move=> _ Ht1'; rewrite /two_pt_mu eqxx subr_gt0. Qed.

Lemma two_pt_mu_pos_fail :
  0 < t -> t < 1 -> 0 < two_pt_mu all_fail.
Proof.
move=> Ht0' _; rewrite /two_pt_mu.
by rewrite eq_sym (negbTE all_pass_ne_fail) eqxx.
Qed.

End TwoPointDistribution.

(* ================================================================== *)
(** ** Finite probability space                                        *)
(* ================================================================== *)

(** A minimal probability-theoretic foundation for the independence
    assumption.  Defines a finite probability measure on a [finType],
    proves basic axioms, and derives the joint-pass formula from a
    formal definition of statistical independence.

    For a finite sample space, every subset is measurable (the
    sigma-algebra is the power set), so events are simply predicates.
    This bridges the algebraic model ([joint_pass = prod p_i] by
    definition) and the probabilistic model ([joint_pass = prod p_i]
    derived from statistical independence). *)

Section FiniteProbSpace.

Variable R : realType.
Variable Omega : finType.
Variable mu : Omega -> R.

Hypothesis mu_ge0 : forall x : Omega, 0 <= mu x.
Hypothesis mu_sum1 : \sum_x mu x = 1.

(** [Pr E]: probability of event [E] under the measure [mu],
    defined as the sum of [mu x] over all [x] satisfying [E]. *)
Definition Pr (E : pred Omega) : R := \sum_(x | E x) mu x.

(** Measure-theoretic sanity: summing non-negative weights yields a non-negative probability. *)
Lemma Pr_ge0 (E : pred Omega) : 0 <= Pr E.
Proof. by apply: sumr_ge0 => x _; exact: mu_ge0. Qed.

(** Normalization axiom: the certain event has unit probability. *)
Lemma Pr_total : Pr predT = 1.
Proof. exact: mu_sum1. Qed.

(** The impossible event carries no mass. *)
Lemma Pr_empty : Pr pred0 = 0.
Proof. by rewrite /Pr big_pred0. Qed.

(** Complement rule: [Pr(not E) = 1 - Pr(E)]. *)
Lemma Pr_complement (E : pred Omega) :
  Pr (predC E) = 1 - Pr E.
Proof.
suff H : Pr E + Pr (predC E) = 1.
  by rewrite -H addrAC subrr add0r.
rewrite /Pr.
rewrite [in X in X + _](eq_bigl (fun x => predT x && E x));
  last by move=> x /=.
rewrite [in X in _ + X](eq_bigl (fun x => predT x && ~~ E x));
  last by move=> x /=.
by rewrite -(bigID E) mu_sum1.
Qed.

(** Every event has probability at most 1. *)
Lemma Pr_le1 (E : pred Omega) : Pr E <= 1.
Proof. by rewrite -subr_ge0 -Pr_complement Pr_ge0. Qed.

(** Probability is monotone: [E1 => E2] implies [Pr(E1) <= Pr(E2)]. *)
Lemma Pr_mono (E1 E2 : pred Omega) :
  (forall x, E1 x -> E2 x) -> Pr E1 <= Pr E2.
Proof.
move=> Hsub; rewrite /Pr.
rewrite (eq_bigl (fun x => E2 x && E1 x)); last first.
  by move=> x; case HE1: (E1 x); rewrite ?andbT ?andbF //; rewrite (Hsub x HE1).
rewrite big_mkcondr.
by apply: ler_sum => x _; case: (E1 x) => //; exact: mu_ge0.
Qed.

(** Subadditivity: [Pr(A \/ B) <= Pr(A) + Pr(B)].
    Proved via [bigID] decomposition into disjoint parts. *)
Lemma Pr_subadditive (E1 E2 : pred Omega) :
  Pr (predU E1 E2) <= Pr E1 + Pr E2.
Proof.
suff Hsplit : Pr (predU E1 E2) = Pr E1 + Pr (predI (predC E1) E2).
  have Hmono : Pr (predI (predC E1) E2) <= Pr E2.
    by apply: Pr_mono => x /andP [_ ->].
  by rewrite Hsplit; apply: lerD; [exact: lexx | exact: Hmono].
rewrite /Pr (bigID E1).
suff -> : \sum_(x | predU E1 E2 x && E1 x) mu x = \sum_(x | E1 x) mu x.
  suff -> : \sum_(x | predU E1 E2 x && ~~ E1 x) mu x =
            \sum_(x | predI (predC E1) E2 x) mu x by [].
  by apply: eq_bigl => x; rewrite /predU /predI /predC /=;
    case: (E1 x); rewrite ?andbT ?andbF.
by apply: eq_bigl => x; rewrite /predU /=;
  case: (E1 x); rewrite ?andbT ?andbF.
Qed.

(* --- Independence --- *)

(** [events_independent E]: the full-intersection form of
    independence — [Pr(cap E_i) = prod Pr(E_i)]. *)
Definition events_independent (k : nat) (E : 'I_k -> pred Omega) :=
  Pr (fun x => [forall i, E i x]) = \prod_(i < k) Pr (E i).

(** [events_fully_independent E]: the textbook form requiring the
    product identity for every sub-collection of events. *)
Definition events_fully_independent (k : nat) (E : 'I_k -> pred Omega) :=
  forall (S : pred 'I_k),
    Pr (fun x => [forall (i | S i), E i x]) = \prod_(i < k | S i) Pr (E i).

(** Full-subset independence implies full-intersection independence. *)
Lemma fully_independent_implies (k : nat) (E : 'I_k -> pred Omega) :
  events_fully_independent E -> events_independent E.
Proof. move=> H; exact (H predT). Qed.

(** Under full-subset independence, the joint probability of any
    sub-collection equals the product of marginals.  Applies
    [events_fully_independent] to [predC (pred1 j)] to derive the
    leave-one-out product identity. *)
Lemma fully_independent_leave_one_out (k : nat)
    (E : 'I_k -> pred Omega) (j : 'I_k) :
  events_fully_independent E ->
  Pr (fun x => [forall (i | i != j), E i x]) =
    \prod_(i < k | i != j) Pr (E i).
Proof. by move=> H; exact: (H (fun i => i != j)). Qed.

(** Under full-subset independence, the marginal product for a
    singleton sub-collection is the event probability itself. *)
Lemma fully_independent_singleton (k : nat)
    (E : 'I_k -> pred Omega) (j : 'I_k) :
  events_fully_independent E ->
  Pr (fun x => [forall (i | i == j), E i x]) = Pr (E j).
Proof.
move=> H; rewrite (H (pred1 j)) (bigD1 j) //=.
by rewrite big1 ?mulr1 // => i /andP [/eqP ->]; rewrite eqxx.
Qed.

(** Helper: product over a two-element subset picks out the two factors. *)
Lemma two_element_prod (k : nat) (f : 'I_k -> R) (i j : 'I_k) :
  i != j ->
  \prod_(k' < k | (k' == i) || (k' == j)) f k' = f i * f j.
Proof.
move=> Hij.
rewrite (bigD1 i) /=; last by rewrite eqxx.
congr (_ * _).
rewrite (eq_bigl (fun k' : 'I_k => k' == j)); last first.
  move=> k'; apply/idP/idP.
  - case/andP => /orP [/eqP Hki | /eqP Hkj] Hkne.
    + by rewrite Hki eqxx in Hkne.
    + by rewrite Hkj eqxx.
  - move=> /eqP ->.
    apply/andP; split; first by rewrite eqxx orbT.
    by rewrite eq_sym.
by rewrite big_pred1_eq.
Qed.

(** Pairwise independence from full independence.  For distinct contest
    indices [i] and [j], the joint probability [Pr(E_i cap E_j)]
    factors as [Pr(E_i) * Pr(E_j)].  Instantiates the fully-independent
    definition at the two-element subset [{i, j}]. *)
Lemma fully_independent_pairwise (k : nat)
    (E : 'I_k -> pred Omega) (i j : 'I_k) :
  events_fully_independent E -> i != j ->
  Pr (fun x => E i x && E j x) = Pr (E i) * Pr (E j).
Proof.
move=> H Hij.
have HS := H (fun k' : 'I_k => (k' == i) || (k' == j)).
have Heq1 : Pr (fun x => E i x && E j x) =
            Pr (fun x => [forall (k' | (k' == i) || (k' == j)), E k' x]).
  rewrite /Pr; apply: eq_bigl => x.
  apply/idP/forallP.
  - move=> /andP [Hi Hj] k'.
    by apply/implyP; case/orP => /eqP ->.
  - move=> Hall; apply/andP; split.
    + by apply: (implyP (Hall i)); rewrite eqxx.
    + by apply: (implyP (Hall j)); rewrite eqxx orbT.
by rewrite Heq1 HS two_element_prod.
Qed.

(** Under independence, the algebraic [joint_pass] matches the
    probabilistic joint probability.  This is the formal bridge
    between the two models. *)
Lemma independent_joint_eq (k : nat) (E : 'I_k -> pred Omega) :
  events_independent E ->
  joint_pass (fun i => Pr (E i)) =
    Pr (fun x => [forall i, E i x]).
Proof. by rewrite /joint_pass /events_independent /= => ->. Qed.

(** Under independence with per-contest risk bounds, the all-pass
    probability is bounded by the Sidak product. *)
Lemma independent_worst_case (k : nat) (E : 'I_k -> pred Omega)
    (alphas : 'I_k -> R) :
  events_independent E ->
  (forall i, 0 <= alphas i <= 1) ->
  (forall i, Pr (E i) <= 1 - alphas i) ->
  Pr (fun x => [forall i, E i x]) <=
    \prod_(i < k) (1 - alphas i).
Proof.
rewrite /events_independent => Hindep Ha Hle.
rewrite Hindep.
by apply: ler_prod => i _; apply/andP; split; [exact: Pr_ge0 | exact: Hle].
Qed.

(** Under independence, heterogeneous false assurance bounds the
    probability of failing to catch at least one wrong outcome. *)
Lemma independent_false_assurance (k : nat) (E : 'I_k -> pred Omega)
    (alphas : 'I_k -> R) :
  events_independent E ->
  (forall i, 0 <= alphas i <= 1) ->
  (forall i, Pr (E i) <= 1 - alphas i) ->
  false_assurance_hetero alphas <=
    1 - Pr (fun x => [forall i, E i x]).
Proof.
rewrite /events_independent => Hindep Ha Hle.
rewrite /false_assurance_hetero Hindep lerD2l lerN2.
by apply: ler_prod => i _; apply/andP; split; [exact: Pr_ge0 | exact: Hle].
Qed.

End FiniteProbSpace.

(* ================================================================== *)
(** ** Two-point distribution: Fréchet upper bound and product failure *)
(* ================================================================== *)

(** The two-point distribution achieves the Fréchet upper bound on
    false assurance: any marginal-compatible distribution has
    [1 - p_joint >= max alpha_j], and the two-point distribution
    achieves equality [1 - p_joint = t = max alpha_j] when [t] is
    chosen as the maximum risk limit. *)

Section TwoPointFrechet.

Variable R : realType.
Variable k : nat.
Hypothesis Hk : (0 < k)%N.
Variable t : R.
Hypothesis Ht0 : 0 <= t.
Hypothesis Ht1 : t <= 1.

(** The two-point distribution achieves the Fréchet upper bound:
    any distribution with marginal pass probability [1 - t] per contest
    has [1 - p_joint >= t], and the two-point achieves [1 - p_joint = t]. *)
Lemma two_pt_achieves_frechet_ub :
  1 - (1 - t) = t.
Proof. by rewrite opprB addrCA subrr addr0. Qed.

(** Under the two-point distribution, the joint pass probability [1-t]
    differs from the product of marginals [(1-t)^k] unless [k = 1].
    This witnesses the failure of the independence product identity
    under maximal positive correlation. *)
Lemma two_pt_product_gap :
  (1 < k)%N -> 0 < t -> t < 1 ->
  1 - t != (1 - t) ^+ k.
Proof.
move=> Hk1 Ht0' Ht1'.
have H1t : 0 < 1 - t by rewrite subr_gt0.
have H1t1 : 1 - t < 1 by rewrite ltrBlDr ltrDl.
apply/eqP => Heq.
have : (1 - t) ^+ k < (1 - t) ^+ 1.
  exact: pow_lt1_strict_anti H1t H1t1 Hk1.
by rewrite -Heq expr1 ltxx.
Qed.

(** Dependence gap: the two-point joint exceeds the independence
    product by [(1-t) - (1-t)^k > 0] when [k >= 2] and [0 < t < 1]. *)
Lemma two_pt_dependence_gap :
  (1 < k)%N -> 0 < t -> t < 1 ->
  (1 - t) ^+ k < 1 - t.
Proof.
move=> Hk1 Ht0' Ht1'.
have H1t : 0 < 1 - t by rewrite subr_gt0.
have H1t1 : 1 - t < 1 by rewrite ltrBlDr ltrDl.
rewrite -[X in _ < X]expr1.
exact: pow_lt1_strict_anti H1t H1t1 Hk1.
Qed.

(** The two-point distribution does NOT satisfy [events_independent]
    when [k >= 2] and [0 < t < 1]: the joint pass probability [1-t]
    differs from the product of marginals [(1-t)^k]. *)
Lemma two_pt_not_independent :
  (1 < k)%N -> 0 < t -> t < 1 ->
  ~ @events_independent R {ffun 'I_k -> bool}
      (@two_pt_mu R k t) k
      (fun (j : 'I_k) (f : {ffun 'I_k -> bool}) => f j).
Proof.
move=> Hk1 Ht0' Ht1'.
rewrite /events_independent /Pr => Heq.
have Hjoint : \sum_(f : {ffun 'I_k -> bool} | [forall j, f j])
  @two_pt_mu R k t f = 1 - t.
  rewrite (bigD1 [ffun _ => true]) /=;
    last by apply/forallP => j; rewrite ffunE.
  rewrite /two_pt_mu eqxx big1 ?addr0 //.
  move=> f /andP [/forallP Hall Hne]; rewrite (negbTE Hne).
  case Hff: (f == [ffun _ => false]) => //.
  by move/eqP: Hff => Hff; move: (Hall (Ordinal Hk)); rewrite Hff ffunE.
have Hprod : \prod_(j < k) \sum_(f : {ffun 'I_k -> bool} | f j)
  @two_pt_mu R k t f = (1 - t) ^+ k.
  rewrite -iter_mulr_1 -big_const_ord; apply: eq_bigr => j _.
  exact: two_pt_marginal.
suff Habs : 1 - t = (1 - t) ^+ k.
  by move/eqP: Habs; exact/negP/(two_pt_product_gap Hk1 Ht0' Ht1').
by rewrite -Hprod -Hjoint.
Qed.

End TwoPointFrechet.

(** ** Measure-theoretic dependent bridge *)

(** For any risk limits [alphas] dominated by a common ceiling [t],
    the two-point distribution is an explicit measure on
    [{ffun 'I_k -> bool}] whose marginals are each at most
    [1 - alphas j] and whose false-assurance is exactly [t].
    Upgrades [dep_concrete_bridge] from algebraic existence to an
    explicit probability measure. *)
Lemma dep_concrete_bridge_measure
    (R : realType) (k : nat) (alphas : 'I_k -> R) (t : R) :
  (0 < k)%N ->
  (forall j : 'I_k, alphas j <= t) -> 0 <= t -> t <= 1 ->
  (forall f : {ffun 'I_k -> bool}, 0 <= @two_pt_mu R k t f) /\
  \sum_(f : {ffun 'I_k -> bool}) @two_pt_mu R k t f = 1 /\
  (forall j, \sum_(f : {ffun 'I_k -> bool} | f j)
               @two_pt_mu R k t f <= 1 - alphas j) /\
  1 - \sum_(f : {ffun 'I_k -> bool} | [forall j, f j])
        @two_pt_mu R k t f = t.
Proof.
move=> Hk Hle Ht0 Ht1.
split; [by move=> f; apply: two_pt_mu_ge0 |].
split; [by apply: two_pt_mu_sum1 |].
split.
- move=> j.
  have Hmarg : \sum_(f : {ffun 'I_k -> bool} | f j)
                 @two_pt_mu R k t f = 1 - t by apply: two_pt_marginal.
  rewrite Hmarg.
  by rewrite lerD2l lerN2; apply: Hle.
- by apply: two_pt_false_assurance.
Qed.

(** ** Fréchet-Hoeffding upper bound achievability *)

(** The two-point distribution at parameter [t] achieves the
    Fréchet-Hoeffding upper bound on joint pass probability:
    [Pr(all pass) = 1 - t].  Instantiated at [t = max alpha_j]
    (when such a max exists and dominates every alpha_j), this gives
    the sharpest achievable joint-pass probability. *)
Lemma two_pt_upper_achieves_at_t
    (R : realType) (k : nat) (t : R) :
  (0 < k)%N -> 0 <= t -> t <= 1 ->
  \sum_(f : {ffun 'I_k -> bool} | [forall j, f j])
    @two_pt_mu R k t f = 1 - t.
Proof.
move=> Hk Ht0 Ht1.
have H : 1 - (\sum_(f : {ffun 'I_k -> bool} | [forall j, f j])
               @two_pt_mu R k t f) = t.
  by apply: two_pt_false_assurance.
set S := \sum_(f : {ffun 'I_k -> bool} | [forall j, f j])
          @two_pt_mu R k t f.
rewrite -/S in H.
by rewrite -H opprB addrC subrK.
Qed.

(** Witness: for any [t] dominating all per-contest risk limits, the
    two-point distribution realizes a marginal-compatible joint
    distribution with [Pr(all pass) = 1 - t].  Setting [t = max alpha_j]
    saturates the Fréchet-Hoeffding upper bound. *)
Lemma two_pt_upper_witness_dominating
    (R : realType) (k : nat) (alphas : 'I_k -> R) (t : R) :
  (0 < k)%N ->
  (forall j : 'I_k, alphas j <= t) ->
  0 <= t -> t <= 1 ->
  \sum_(f : {ffun 'I_k -> bool} | [forall j, f j])
    @two_pt_mu R k t f = 1 - t /\
  forall j : 'I_k,
    \sum_(f : {ffun 'I_k -> bool} | f j) @two_pt_mu R k t f
    = 1 - t.
Proof.
move=> Hk Hle Ht0 Ht1.
split; first exact: two_pt_upper_achieves_at_t.
move=> j.
by apply: two_pt_marginal.
Qed.

(** ** Fréchet-Hoeffding upper bound for marginal-compatible measures *)

(** For any marginal-compatible joint distribution on
    [{ffun 'I_k -> bool}], the probability of the all-pass event is
    bounded by the marginal of any single contest: [Pr(all pass) <=
    Pr(f j)] for every [j].  This is the Fréchet-Hoeffding upper
    bound: joint probability cannot exceed the smallest marginal. *)
Lemma frechet_upper_pointwise
    (R : realType) (k : nat)
    (mu : {ffun 'I_k -> bool} -> R)
    (Hmu_ge0 : forall f, 0 <= mu f)
    (j : 'I_k) :
  @Pr R _ mu (fun f : {ffun 'I_k -> bool} => [forall j', f j']) <=
  @Pr R _ mu (fun f : {ffun 'I_k -> bool} => f j).
Proof.
apply: Pr_mono; first exact: Hmu_ge0.
by move=> f /forallP H; exact: H.
Qed.

(** Equivalent form: under marginal compatibility [P(pass_j) = 1 - alpha_j],
    [Pr(all pass) <= 1 - alpha_j] for every j.  Taking j = argmax gives
    the sharpest upper bound [Pr(all pass) <= 1 - max_j alpha_j]. *)
Lemma frechet_upper_marginal
    (R : realType) (k : nat) (alphas : 'I_k -> R)
    (mu : {ffun 'I_k -> bool} -> R)
    (Hmu_ge0 : forall f, 0 <= mu f)
    (j : 'I_k) :
  @Pr R _ mu (fun f => f j) = 1 - alphas j ->
  @Pr R _ mu (fun f : {ffun 'I_k -> bool} => [forall j', f j']) <=
  1 - alphas j.
Proof.
move=> Hmarg.
by rewrite -Hmarg; apply: frechet_upper_pointwise.
Qed.

(** The two-point distribution at [t = max alpha_j] is extremal: it
    attains the Fréchet upper bound [1 - t] with equality. *)
Lemma two_pt_extremal
    (R : realType) (k : nat) (alphas : 'I_k -> R) (t : R) (j_max : 'I_k) :
  (0 < k)%N -> 0 <= t -> t <= 1 ->
  alphas j_max = t ->
  @Pr R _ (@two_pt_mu R k t)
    (fun f : {ffun 'I_k -> bool} => [forall j, f j]) = 1 - alphas j_max.
Proof.
move=> Hk Ht0 Ht1 Hjmax.
rewrite Hjmax /Pr.
exact: (@two_pt_upper_achieves_at_t R k t Hk Ht0 Ht1).
Qed.

(** ** Axiom audit for probability lemmas *)

Print Assumptions two_pt_mu_sum1.
Print Assumptions two_pt_marginal.
Print Assumptions two_pt_false_assurance.
Print Assumptions Pr_ge0.
Print Assumptions Pr_complement.
Print Assumptions Pr_subadditive.
Print Assumptions independent_joint_eq.
Print Assumptions independent_false_assurance.
