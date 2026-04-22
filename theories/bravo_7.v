(******************************************************************************)
(*                                                                            *)
(*     BRAVO ballot-polling audit as a supermartingale instantiation          *)
(*                                                                            *)
(*     Defines the likelihood-ratio test martingale for a binary ballot      *)
(*     model and connects it to the degradation theory via Ville's           *)
(*     inequality.  Establishes:                                              *)
(*       - The likelihood ratio is a non-negative martingale under the null  *)
(*       - Per-contest risk bound follows from Ville's inequality            *)
(*       - The degradation bound holds for any collection of BRAVO tests    *)
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
Close Scope N_scope.
Open Scope ring_scope.

From Auditing Require Import auditing_1 probability_4 ville_6.

Strategy 1000 [cond_exp Exp].

(** ** Risk-limited test abstraction *)

Section RiskLimitedTest.

Variable R : realType.

(** [risk_limited_test]: a record capturing everything needed for a
    per-contest risk bound via the supermartingale method.  Bundles a
    finite sample space, a probability measure, a filtration, a
    non-negative supermartingale with initial expectation at most 1,
    and a risk limit in (0,1). *)
Record risk_limited_test := RiskLimitedTest {
  rlt_Omega : finType;
  rlt_mu : rlt_Omega -> R;
  rlt_mu_ge0 : forall x, 0 <= rlt_mu x;
  rlt_mu_sum1 : \sum_x rlt_mu x = 1;
  rlt_F : nat -> rlt_Omega -> rlt_Omega -> bool;
  rlt_M : nat -> rlt_Omega -> R;
  rlt_filtration : @filtration rlt_Omega rlt_F;
  rlt_supermg : @supermartingale R rlt_Omega rlt_mu rlt_F rlt_M;
  rlt_nonneg : forall k x, 0 <= rlt_M k x;
  rlt_Exp0 : @Exp R rlt_Omega rlt_mu (rlt_M 0) <= 1;
  rlt_alpha : R;
  rlt_alpha_pos : 0 < rlt_alpha;
  rlt_alpha_lt1 : rlt_alpha < 1;
}.

(** [rlt_ville T n]: Ville's inequality instantiated for a risk-limited
    test [T] at time [n].  The probability that the test statistic [M_n]
    exceeds [1/alpha] is at most [alpha]. *)
Lemma rlt_ville (T : risk_limited_test) (n : nat)
    (Hcell : forall k (x : rlt_Omega T),
       0 < \sum_(y | rlt_F k x y) rlt_mu y) :
  @Pr R _ (rlt_mu (r:=T)) (fun x => (rlt_alpha T)^-1 <= rlt_M n x)
    <= rlt_alpha T.
Proof.
exact: (ville_ineq (rlt_mu_ge0 (r:=T)) n
          (rlt_filtration T) (rlt_supermg T)
          Hcell (rlt_nonneg (r:=T))
          (rlt_alpha_pos T) (rlt_alpha_lt1 T) (rlt_Exp0 T)).
Qed.

End RiskLimitedTest.

(** ** Binary ballot model and single-step likelihood ratio *)

Section BinaryBallot.

Variable R : realType.

(** [p]: the null-hypothesis win probability, assumed to exceed 1/2.
    Under the null, the reported winner truly won a majority. *)
Variable p : R.
Hypothesis Hp_gt_half : 2%:R^-1 < p.
Hypothesis Hp_lt1 : p < 1.

(** Basic consequences of the hypotheses on [p]. *)

(** [p] is positive. *)
Lemma p_pos : 0 < p.
Proof.
apply: (lt_trans _ Hp_gt_half).
by rewrite invr_gt0 ltr0n.
Qed.

(** [1 - p] is positive. *)
Lemma q_pos : 0 < 1 - p.
Proof. by rewrite subr_gt0. Qed.

(** [p] is not zero. *)
Lemma p_neq0 : p != 0.
Proof. by rewrite gt_eqF // p_pos. Qed.

(** [1 - p] is not zero. *)
Lemma q_neq0 : 1 - p != 0.
Proof. by rewrite gt_eqF // q_pos. Qed.

(** [ballot_mu b]: the null-hypothesis measure on [bool].
    [true] (win) has mass [p]; [false] (lose) has mass [1 - p]. *)
Definition ballot_mu (b : bool) : R :=
  if b then p else 1 - p.

(** The ballot measure is non-negative. *)
Lemma ballot_mu_ge0 (b : bool) : 0 <= ballot_mu b.
Proof.
by rewrite /ballot_mu; case: b; [exact: ltW p_pos | exact: ltW q_pos].
Qed.

(** The ballot measure sums to 1. *)
Lemma ballot_mu_sum1 : \sum_b ballot_mu b = 1.
Proof.
by rewrite big_bool /ballot_mu /= addrC subrK.
Qed.

(** [lr b]: the single-step likelihood ratio for ballot outcome [b].
    Under the alternative (fair coin), both outcomes have probability 1/2.
    Under the null, win has probability [p] and lose has probability [1 - p].
    So [lr(win) = (1/2)/p] and [lr(lose) = (1/2)/(1-p)]. *)
Definition lr (b : bool) : R :=
  if b then 2%:R^-1 / p else 2%:R^-1 / (1 - p).

(** The likelihood ratio is non-negative. *)
Lemma lr_ge0 (b : bool) : 0 <= lr b.
Proof.
rewrite /lr; case: b.
- apply: divr_ge0; first by rewrite invr_ge0 ler0n.
  exact: ltW p_pos.
- apply: divr_ge0; first by rewrite invr_ge0 ler0n.
  exact: ltW q_pos.
Qed.

(** ** The fundamental martingale identity: E_null[L] = 1 *)

(** Under the null hypothesis, the expected value of the single-step
    likelihood ratio is exactly 1.  This is the defining property that
    makes the sequential product a martingale. *)
Lemma lr_expectation_1 : \sum_b ballot_mu b * lr b = 1.
Proof.
rewrite big_bool /ballot_mu /lr /=.
rewrite mulrCA (mulfV p_neq0) mulr1.
rewrite mulrCA (mulfV q_neq0) mulr1.
suff -> : 2%:R^-1 = 1 / 2%:R :> R by rewrite -splitr.
by rewrite mul1r.
Qed.

(** Equivalent statement: the expectation under [Exp] equals 1. *)
Lemma lr_Exp_eq1 : @Exp R _ ballot_mu lr = 1.
Proof. exact: lr_expectation_1. Qed.

(** The likelihood ratio for a win is positive. *)
Lemma lr_win_pos : 0 < lr true.
Proof.
rewrite /lr divr_gt0 //.
  by rewrite invr_gt0 ltr0n.
exact: p_pos.
Qed.

(** The likelihood ratio for a loss is positive. *)
Lemma lr_lose_pos : 0 < lr false.
Proof.
rewrite /lr divr_gt0 //.
  by rewrite invr_gt0 ltr0n.
exact: q_pos.
Qed.

(** The likelihood ratio for a win is below 1 when [p > 1/2]:
    wins are expected under the null and reduce the test statistic. *)
Lemma lr_win_lt1 : lr true < 1.
Proof.
rewrite /lr ltr_pdivrMr; last exact: p_pos.
by rewrite mul1r.
Qed.

(** The likelihood ratio for a loss exceeds 1 when [p > 1/2]:
    losses are unexpected under the null and raise the test statistic. *)
Lemma half_complement : 1 - 2%:R^-1 = 2%:R^-1 :> R.
Proof.
have H2 : 2%:R != (0 : R) by rewrite pnatr_eq0.
have Hhalf : 2%:R^-1 + 2%:R^-1 = 1 :> R.
  by apply: (mulfI H2); rewrite mulrDr !mulfV // mulr1 -mulr2n.
by rewrite -{1}Hhalf addrK.
Qed.

Lemma lr_lose_gt1 : 1 < lr false.
Proof.
rewrite /lr ltr_pdivlMr ?q_pos // mul1r -half_complement.
by rewrite ltrD2l ltrN2.
Qed.

End BinaryBallot.

(** ** Degradation connection: per-contest bounds imply joint bounds *)

Section DegradationConnection.

Variable R : realType.

(** [degradation_from_per_contest k alphas pass_probs]: the core
    connection theorem.  If each contest [i] has a pass probability
    (probability that the audit does NOT reject, under the null)
    bounded above by [1 - alphas i], then the joint pass probability
    is bounded by [prod (1 - alphas i)], and hence the joint false
    assurance is bounded by [false_assurance_hetero alphas].

    This is the mechanism-independence theorem: the degradation bound
    depends only on the per-contest risk guarantee, not on the internal
    structure of the test.  BRAVO, Wald's SPRT, Bayesian audits, and
    any other method that provides a valid per-contest bound all feed
    into the same degradation formula. *)
Lemma degradation_from_per_contest (k : nat)
    (alphas : 'I_k -> R) (pass_probs : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  (forall i, 0 <= pass_probs i <= 1 - alphas i) ->
  1 - joint_pass pass_probs >= false_assurance_hetero alphas.
Proof.
move=> Ha Hps.
rewrite /false_assurance_hetero /joint_pass.
rewrite lerD2l lerN2.
apply: ler_prod => i _.
by move: (Hps i) => /andP [H0 H1]; rewrite H0 H1.
Qed.

End DegradationConnection.

(** ** Trivial (discrete) filtration construction *)

Section TrivialFiltration.

Variable Omega : finType.

(** [trivial_filtration]: the discrete filtration where every element
    is equivalent only to itself.  In a sequential test with fully
    observed draws, [F_n] is the discrete sigma-algebra for all [n]. *)
Definition trivial_filtration (n : nat) (x y : Omega) : bool :=
  x == y.

(** The trivial filtration is a valid filtration. *)
Lemma trivial_filtration_ok :
  @filtration Omega trivial_filtration.
Proof.
split.
- by move=> n x; rewrite /trivial_filtration eqxx.
- by move=> n x y; rewrite /trivial_filtration eq_sym.
- by move=> n x y z; rewrite /trivial_filtration => /eqP -> /eqP ->.
- by move=> n x y; rewrite /trivial_filtration.
Qed.

End TrivialFiltration.

(** ** Trivial-filtration martingale properties *)

Section TrivialFiltrationMartingale.

Variable R : realType.
Variable Omega : finType.
Variable mu : Omega -> R.
Hypothesis mu_ge0 : forall x, 0 <= mu x.
Hypothesis mu_sum1 : \sum_x mu x = 1.

(* Section-local copy of the trivial filtration, avoiding the
   implicit-argument mismatch between the TrivialFiltration section's
   Omega parameter and this section's Omega variable. *)
Let tf : nat -> Omega -> Omega -> bool := fun n x y => x == y.

(** Under the trivial filtration, conditional expectation of any function
    at any point reduces to the function value itself (since each cell
    is a singleton). *)
Lemma trivial_cond_exp (X : Omega -> R) (n : nat) (x : Omega) :
  0 < mu x ->
  cond_exp mu tf X n x = X x.
Proof.
move=> Hmu_pos.
have Hne : mu x != 0 by apply/eqP => H0; rewrite H0 ltxx in Hmu_pos.
rewrite /cond_exp /tf.
rewrite (bigD1 x) //= big1 ?addr0; last first.
  by move=> y /andP [/eqP -> /negPf]; rewrite eqxx.
rewrite [in X in _ / X](bigD1 x) //= big1 ?addr0; last first.
  by move=> y /andP [/eqP -> /negPf]; rewrite eqxx.
by rewrite mulrAC divrr ?mul1r // unitfE.
Qed.

(** A constant process is a martingale under the trivial filtration. *)
Lemma const_martingale (c : R) :
  (forall x, 0 < mu x) ->
  martingale mu tf (fun _ _ => c).
Proof.
move=> H; split.
- by move=> n x y _.
- by move=> n x; rewrite trivial_cond_exp.
Qed.

(** A constant process is a supermartingale under the trivial filtration. *)
Lemma const_supermartingale (c : R) :
  (forall x, 0 < mu x) ->
  supermartingale mu tf (fun _ _ => c).
Proof.
move=> H; split.
- by move=> n x y _.
- by move=> n x; rewrite trivial_cond_exp.
Qed.

End TrivialFiltrationMartingale.

(** ** N-step product martingale *)

Section ProductMartingale.

Variable R : realType.

(** [product_lr p bs n]: the cumulative likelihood ratio after [n] ballot
    draws, where [bs : nat -> bool] records the outcome sequence (true = win).
    This is the product [L_1 * L_2 * ... * L_n], where each [L_i] is the
    single-step likelihood ratio.

    In the BRAVO protocol, the audit rejects (declares the election
    correct) when this product exceeds [1/alpha].  Ville's inequality
    guarantees that under the null hypothesis, this event has probability
    at most [alpha]. *)
Definition product_lr (p : R) (bs : nat -> bool) (n : nat) : R :=
  \prod_(i < n) lr p (bs i).

(** The product likelihood ratio at step 0 is 1. *)
Lemma product_lr_0 (p : R) (bs : nat -> bool) :
  product_lr p bs 0 = 1.
Proof. by rewrite /product_lr big_ord0. Qed.

(** The product likelihood ratio is non-negative. *)
Lemma product_lr_ge0 (p : R) (bs : nat -> bool) (n : nat) :
  2%:R^-1 < p -> p < 1 ->
  0 <= product_lr p bs n.
Proof.
move=> Hp Hp1; rewrite /product_lr; apply: prodr_ge0 => i _.
exact: lr_ge0.
Qed.

(** The product likelihood ratio at step [n+1] factors as the step-[n]
    value times the new single-step ratio. *)
Lemma product_lr_step (p : R) (bs : nat -> bool) (n : nat) :
  product_lr p bs n.+1 = product_lr p bs n * lr p (bs n).
Proof. by rewrite /product_lr big_ord_recr. Qed.

(** [product_lr_Exp0_le1]: the initial expectation of the product
    likelihood ratio is at most 1.  This is the base case that
    feeds into Ville's inequality via [rlt_ville].

    The N-step martingale property (E[product_lr(n+1) | F_n] =
    product_lr(n)) follows from [multiplicative_martingale_step]
    (below): since product_lr(n+1) = product_lr(n) * lr(x_n) where
    product_lr(n) is F_n-measurable and E[lr | F_n] = 1 by the
    conditional independence of the n-th ballot draw. *)
Lemma product_lr_Exp0_le1 (p : R) (n : nat) :
  2%:R^-1 < p -> p < 1 ->
  forall (Omega : finType) (mu : Omega -> R)
    (mu_ge0 : forall x, 0 <= mu x) (mu_sum1 : \sum_x mu x = 1)
    (outcome : Omega -> nat -> bool),
    (forall x, product_lr p (outcome x) 0 = 1) ->
    @Exp R _ mu (fun x => product_lr p (outcome x) 0) <= 1.
Proof.
move=> Hp Hp1 Omega0 mu0 Hge0 Hsum1 outcome H0.
have -> : (fun x => product_lr p (outcome x) 0) = (fun _ => (1 : R)).
  by apply: boolp.funext => x; rewrite H0.
rewrite /Exp (eq_bigr (fun x => mu0 x)); last by move=> x _; rewrite mulr1.
by rewrite Hsum1.
Qed.

End ProductMartingale.

(** ** Product likelihood ratio: initial expectation bound (refactored) *)

Section ProductLRExp0.

Variable R : realType.
Variable p : R.
Hypothesis Hp : 2%:R^-1 < p.
Hypothesis Hp1 : p < 1.
Variable Omega : finType.
Variable mu : Omega -> R.
Hypothesis mu_ge0 : forall x, 0 <= mu x.
Hypothesis mu_sum1 : \sum_x mu x = 1.
Variable outcome : Omega -> nat -> bool.

(** Initial expectation of the product likelihood ratio is at most 1,
    given that [product_lr] starts at 1 for every sample point. *)
Lemma product_lr_Exp0_le1' :
  (forall x, product_lr p (outcome x) 0 = 1) ->
  @Exp R _ mu (fun x => product_lr p (outcome x) 0) <= 1.
Proof.
move=> H0.
have -> : (fun x => product_lr p (outcome x) 0) = (fun _ => (1 : R)).
  by apply: boolp.funext => x; rewrite H0.
rewrite /Exp (eq_bigr (fun x => mu x)); last by move=> x _; rewrite mulr1.
by rewrite mu_sum1.
Qed.

End ProductLRExp0.

(** ** Degradation connection *)

(** End-to-end: for [k] independent contests, each with a per-contest
    Ville bound, the joint false assurance is bounded by
    [false_assurance_hetero].  The per-contest pass probability under
    the null is [1 - alpha_i] (from Ville), satisfying the
    [degradation_from_per_contest] constraint. *)
Lemma bravo_degradation (R : realType) (k : nat)
    (alphas : 'I_k -> R)
    (pass_probs : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  (forall i, 0 <= pass_probs i <= 1 - alphas i) ->
  false_assurance_hetero alphas <= 1 - joint_pass pass_probs.
Proof. exact: degradation_from_per_contest. Qed.

(** ** Multiplicative martingale step *)

(** The key factorization: if [M] is [F]-measurable and [L] has
    conditional expectation equal to [c] given [F], then the
    conditional expectation of [M * L] given [F] is [M * c].
    Specialized to [c = 1], this gives the martingale step for
    multiplicative processes like the BRAVO likelihood ratio. *)

Section MultiplicativeStep.

Variable R : realType.
Variable Omega : finType.
Variable mu : Omega -> R.
Hypothesis mu_ge0 : forall x, 0 <= mu x.

Variable F_eq : Omega -> Omega -> bool.

(** If [M] is [F]-measurable and [L] is any function, then
    [E[M * L | F](x) = M(x) * E[L | F](x)] when the cell has
    positive mass. *)
Lemma cond_exp_mul_measurable (M L : Omega -> R) (x : Omega) :
  (forall y, F_eq x y -> M y = M x) ->
  0 < \sum_(y | F_eq x y) mu y ->
  @cond_exp R Omega mu (fun _ => F_eq) (fun y => M y * L y) 0 x =
  M x * @cond_exp R Omega mu (fun _ => F_eq) L 0 x.
Proof.
move=> Hmeas Hpos.
rewrite /cond_exp /=.
have -> : \sum_(y | F_eq x y) mu y * (M y * L y) =
          M x * \sum_(y | F_eq x y) mu y * L y.
  rewrite mulr_sumr; apply: eq_bigr => y Hy.
  by rewrite (Hmeas _ Hy) mulrCA.
by rewrite mulrA.
Qed.

(** The martingale step for multiplicative processes: if [M_n] is
    [F_n]-measurable and [E[L | F_n] = 1] uniformly, then
    [E[M_n * L | F_n] = M_n]. *)
Lemma multiplicative_martingale_step (M L : Omega -> R) (x : Omega) :
  (forall y, F_eq x y -> M y = M x) ->
  0 < \sum_(y | F_eq x y) mu y ->
  @cond_exp R Omega mu (fun _ => F_eq) L 0 x = 1 ->
  @cond_exp R Omega mu (fun _ => F_eq) (fun y => M y * L y) 0 x = M x.
Proof.
move=> Hmeas Hpos HL1.
by rewrite cond_exp_mul_measurable // HL1 mulr1.
Qed.

End MultiplicativeStep.

(** ** Summary: the BRAVO-to-degradation pipeline *)

(** The logical chain connecting a single BRAVO test to the degradation
    bound is:

    1. Define the likelihood ratio [lr] on the ballot space.
    2. Prove [E_null[lr] = 1] (the martingale identity, [lr_expectation_1]).
    3. The sequential product inherits the martingale property
       (the single-step identity is the inductive core).
    4. Ville's inequality ([ville_ineq]) gives
       [Pr(product_lr >= 1/alpha) <= alpha].
    5. This per-contest bound plugs into [false_assurance_hetero]
       without any knowledge of the test's internal structure.
    6. The degradation theory ([degradation_from_per_contest]) yields
       the joint false assurance bound for the full election.

    The key insight is the separation of concerns: steps 1-4 are
    specific to the audit protocol, while steps 5-6 are purely
    algebraic and apply to any mechanism that delivers a per-contest
    risk bound.

    The general ballot model below proves the full chain for an
    arbitrary finite candidate type [C], with [swap_at] providing
    the coordinate-swap bijection for cell mass factorization.
    The binary (BRAVO) case follows as the instantiation [C := bool]. *)

Section GeneralBallot.

Variable R : realType.
Variable C : finType.
Variable mu0 : C -> R.
Hypothesis mu0_pos : forall c : C, 0 < mu0 c.
Hypothesis mu0_sum1 : \sum_(c : C) mu0 c = 1.

Variable gen_lr : C -> R.
Hypothesis gen_lr_ge0 : forall c, 0 <= gen_lr c.
Hypothesis gen_lr_exp1 : \sum_(c : C) mu0 c * gen_lr c = 1.

Variable N : nat.
Hypothesis HN : (0 < N)%N.

Definition gen_prod_mu (f : {ffun 'I_N -> C}) : R :=
  \prod_(i < N) mu0 (f i).

Lemma gen_prod_mu_ge0 (f : {ffun 'I_N -> C}) : 0 <= gen_prod_mu f.
Proof. by apply: prodr_ge0 => i _; exact: ltW. Qed.

Lemma gen_prod_mu_pos (f : {ffun 'I_N -> C}) : 0 < gen_prod_mu f.
Proof. by apply: prodr_gt0 => i _. Qed.

Lemma gen_prod_mu_sum1 :
  \sum_(f : {ffun 'I_N -> C}) gen_prod_mu f = 1.
Proof.
rewrite /gen_prod_mu.
have <- : \prod_(i < N) \sum_(c : C) mu0 c =
          \sum_(f : {ffun 'I_N -> C}) \prod_(i < N) mu0 (f i).
  exact: bigA_distr_bigA.
by rewrite (eq_bigr (fun _ => 1)) ?big1_eq // => i _; exact: mu0_sum1.
Qed.

Definition gen_F (n : nat) (x y : {ffun 'I_N -> C}) : bool :=
  [forall i : 'I_N, (i < n)%N ==> (x i == y i)].

Lemma gen_F_refl : forall n, reflexive (@gen_F n).
Proof. by move=> n x; apply/forallP => i; apply/implyP => _; rewrite eqxx. Qed.

Lemma gen_F_sym : forall n, symmetric (@gen_F n).
Proof.
move=> n x y; apply/forallP/forallP => H i;
  by move/(_ i)/implyP: H => H; apply/implyP => Hi; rewrite eq_sym; exact: H.
Qed.

Lemma gen_F_trans : forall n, transitive (@gen_F n).
Proof.
move=> n y x z /forallP Hxy /forallP Hyz.
apply/forallP => i; apply/implyP => Hi.
by rewrite (eqP (implyP (Hxy i) Hi)) (eqP (implyP (Hyz i) Hi)).
Qed.

Lemma gen_F_refine : forall n x y, gen_F n.+1 x y -> gen_F n x y.
Proof.
move=> n x y /forallP H; apply/forallP => i; apply/implyP => Hi.
by apply: (implyP (H i)); exact: ltnW.
Qed.

Lemma gen_filtration : @filtration _ gen_F.
Proof.
by split; [exact: gen_F_refl | exact: gen_F_sym |
           exact: gen_F_trans | exact: gen_F_refine].
Qed.

Lemma gen_F_cell_pos (n : nat) (x : {ffun 'I_N -> C}) :
  0 < \sum_(y | gen_F n x y) gen_prod_mu y.
Proof.
rewrite (bigD1 x); last exact: gen_F_refl.
apply: ltr_pwDl; first exact: gen_prod_mu_pos.
by apply: sumr_ge0 => y _; exact: gen_prod_mu_ge0.
Qed.

Lemma gen_F_split (n : nat) (Hn : (n < N)%N)
    (x f : {ffun 'I_N -> C}) :
  gen_F n.+1 x f = gen_F n x f && (f (Ordinal Hn) == x (Ordinal Hn)).
Proof.
apply/idP/andP.
- move/forallP => H; split.
  + apply/forallP => i; apply/implyP => Hi.
    by apply: (implyP (H i)); exact: leq_trans Hi (leqnSn n).
  + by rewrite eq_sym; apply: (implyP (H (Ordinal Hn))); exact: ltnSn.
- move=> [/forallP Hn_cell /eqP Heq]; apply/forallP => i; apply/implyP.
  rewrite ltnS leq_eqVlt => /orP [/eqP Hi|Hi].
  + have -> : i = Ordinal Hn by apply: val_inj; rewrite /= Hi.
    by rewrite eq_sym; apply/eqP.
  + by exact: (implyP (Hn_cell i)).
Qed.

(** [swap_at j c1 c2 f]: swap values [c1] and [c2] at coordinate [j],
    leaving all other coordinates and values unchanged.  Generalizes
    [flip_at] from [bool] to an arbitrary [finType]. *)
Definition swap_at (j : 'I_N) (c1 c2 : C) (f : {ffun 'I_N -> C})
    : {ffun 'I_N -> C} :=
  [ffun i => if i == j then
    if f i == c1 then c2
    else if f i == c2 then c1
    else f i
  else f i].

Lemma swap_at_invol (j : 'I_N) (c1 c2 : C) :
  involutive (swap_at j c1 c2).
Proof.
move=> f; apply/ffunP => i; rewrite !ffunE.
have [->|_] := eqVneq i j; last by [].
have [->|Hc1] := eqVneq (f j) c1.
  have [->|_] := eqVneq c2 c1; first by [].
  by rewrite eqxx.
have [->|Hc2] := eqVneq (f j) c2.
  by rewrite eqxx.
by rewrite (negbTE Hc1) (negbTE Hc2).
Qed.

Lemma swap_at_inj (j : 'I_N) (c1 c2 : C) :
  injective (swap_at j c1 c2).
Proof.
by move=> a b /(congr1 (swap_at j c1 c2)); rewrite !swap_at_invol.
Qed.

Lemma swap_at_ne (j : 'I_N) (c1 c2 : C)
    (f : {ffun 'I_N -> C}) (i : 'I_N) :
  i != j -> (swap_at j c1 c2 f) i = f i.
Proof. by rewrite ffunE => /negbTE ->. Qed.

Lemma swap_at_eq_c1 (j : 'I_N) (c1 c2 : C)
    (f : {ffun 'I_N -> C}) :
  f j = c1 -> (swap_at j c1 c2 f) j = c2.
Proof. by move=> Hj; rewrite ffunE eqxx Hj eqxx. Qed.

Lemma swap_at_eq_c2 (j : 'I_N) (c1 c2 : C)
    (f : {ffun 'I_N -> C}) :
  f j = c2 -> (swap_at j c1 c2 f) j = c1.
Proof.
move=> Hj; rewrite ffunE eqxx Hj.
by case: eqP => [->|_] //; rewrite eqxx.
Qed.

Lemma swap_at_gen_F (n : nat) (j : 'I_N) (c1 c2 : C)
    (x f : {ffun 'I_N -> C}) :
  (n <= j)%N -> gen_F n x (swap_at j c1 c2 f) = gen_F n x f.
Proof.
move=> Hnj; apply/forallP/forallP => /= H i;
  have /implyP Hi := H i; apply/implyP => Hin;
  have Hij : i != j by [apply: contraTN Hin => /eqP ->; rewrite -leqNgt];
  move: (Hi Hin); by rewrite swap_at_ne.
Qed.

Lemma swap_at_reduced_prod (j : 'I_N) (c1 c2 : C)
    (f : {ffun 'I_N -> C}) :
  \prod_(i < N | i != j) mu0 ((swap_at j c1 c2 f) i) =
  \prod_(i < N | i != j) mu0 (f i).
Proof.
by apply: eq_bigr => i Hij; rewrite swap_at_ne.
Qed.

Strategy 100 [swap_at gen_prod_mu].

(** Cell mass recurrence for the general ballot model. *)
Lemma gen_cell_mass_step (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> C}) :
  \sum_(f | gen_F n.+1 x f) gen_prod_mu f =
  mu0 (x (Ordinal Hn)) *
  \sum_(f | gen_F n x f) gen_prod_mu f.
Proof.
set j := Ordinal Hn.
pose rprod (f : {ffun 'I_N -> C}) := \prod_(i < N | i != j) mu0 (f i).
have Hfactor : forall f : {ffun 'I_N -> C},
  gen_prod_mu f = mu0 (f j) * rprod f.
  by move=> f; rewrite /gen_prod_mu /rprod (bigD1 j).
(* LHS = mu0(x j) * V, with V the rprod-sum over the agree cell. *)
have HL : \sum_(f | gen_F n.+1 x f) gen_prod_mu f =
  mu0 (x j) * \sum_(f | gen_F n x f && (f j == x j)) rprod f.
  rewrite (eq_bigl (fun f => gen_F n x f && (f j == x j))); last first.
    by move=> f; rewrite (gen_F_split Hn).
  rewrite mulr_sumr; apply: eq_bigr => f /andP [_ /eqP Hfj].
  by rewrite Hfactor Hfj.
(* Per-slice rprod sum is independent of c, via swap_at j c (x j). *)
have Hslice : forall c : C,
  \sum_(f | gen_F n x f && (f j == c)) rprod f =
  \sum_(f | gen_F n x f && (f j == x j)) rprod f.
  move=> c.
  have [->|Hcne] := eqVneq c (x j); first by [].
  have Hinj : injective (swap_at j c (x j)) := @swap_at_inj j c (x j).
  rewrite (reindex_inj Hinj).
  apply: eq_big.
  - move=> g; rewrite (@swap_at_gen_F n j c (x j) x g (leqnn n)).
    congr (_ && _); rewrite ffunE eqxx.
    case: (g j =P c) => [-> | /eqP Hgjc].
      exact: eq_sym.
    case: (g j =P x j) => [_ | /eqP _].
      by rewrite !eqxx.
    by rewrite (negbTE Hgjc).
  - move=> g _; rewrite /rprod.
    by apply: eq_bigr => i Hij; rewrite swap_at_ne.
(* Cell_n = V by partitioning over f j and applying Hslice. *)
have HR : \sum_(f | gen_F n x f) gen_prod_mu f =
  \sum_(f | gen_F n x f && (f j == x j)) rprod f.
  transitivity (\sum_(c : C)
    \sum_(f | gen_F n x f && (f j == c)) gen_prod_mu f).
    by rewrite (partition_big (fun f : {ffun 'I_N -> C} => f j) predT) //=.
  transitivity (\sum_(c : C) mu0 c *
    \sum_(f | gen_F n x f && (f j == x j)) rprod f).
    apply: eq_bigr => c _; rewrite -(Hslice c) mulr_sumr.
    by apply: eq_bigr => f /andP [_ /eqP Hfj]; rewrite Hfactor Hfj.
  by rewrite -mulr_suml mu0_sum1 mul1r.
by rewrite HL HR.
Qed.

(** General cell mass formula. *)
Lemma gen_cell_mass (n : nat) (Hn : (n <= N)%N)
    (x : {ffun 'I_N -> C}) :
  \sum_(f : {ffun 'I_N -> C} | gen_F n x f) gen_prod_mu f =
  \prod_(i < N | (i < n)%N) mu0 (x i).
Proof.
elim: n Hn => [|n IH] Hn.
  have -> : \prod_(i < N | (i < 0)%N) mu0 (x i) = 1.
    by apply: big1 => i Hi; rewrite ltn0 in Hi.
  have -> : \sum_(f | gen_F 0 x f) gen_prod_mu f =
            \sum_f gen_prod_mu f.
    apply: eq_bigl => f; apply/forallP => i.
    by apply/implyP => Hi; rewrite ltn0 in Hi.
  exact: gen_prod_mu_sum1.
rewrite (gen_cell_mass_step Hn) (IH (ltnW Hn)).
set j := Ordinal (n:=N) Hn.
rewrite [RHS](bigD1 j) /=; last exact: ltnSn.
congr (mu0 (x j) * _); apply: eq_bigl => i.
by rewrite ltnS -(inj_eq val_inj) /= andbC -ltn_neqAle.
Qed.

(** Coordinate restriction for the general model. *)
Lemma gen_cell_mass_coord (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> C}) (c : C) :
  \sum_(f | gen_F n x f && (f (Ordinal Hn) == c)) gen_prod_mu f =
  mu0 c * \sum_(f | gen_F n x f) gen_prod_mu f.
Proof.
set j := Ordinal Hn.
set Cell := \sum_(f | gen_F n x f) gen_prod_mu f.
have Hsplit : Cell =
  \sum_(f | gen_F n x f && (f j == x j)) gen_prod_mu f +
  \sum_(f | gen_F n x f && (f j != x j)) gen_prod_mu f
  by rewrite -bigID.
have Hagree : \sum_(f | gen_F n x f && (f j == x j)) gen_prod_mu f =
  mu0 (x j) * Cell.
  rewrite -/Cell -(gen_cell_mass_step Hn).
  by apply: eq_bigl => f; rewrite (gen_F_split Hn).
case: (boolP (c == x j)) => [/eqP ->|Hne]; first exact: Hagree.
(* c != x j: use swap_at to reduce to the agree case *)
rewrite -(gen_cell_mass_step Hn) in Hagree.
have Hswap :
  \sum_(f | gen_F n x f && (f j == c)) gen_prod_mu f =
  mu0 c * Cell.
  (* Swap c and x j, then apply Hagree-like argument *)
  set xc := swap_at j (x j) c x.
  have Hxcj : xc j = c by rewrite /xc swap_at_eq_c1.
  (* cell(n+1) for xc = mu0(xc j) * cell(n) for xc *)
  (* But cell(n) for xc = cell(n) for x (same first n coords) *)
  have HcellEq : \sum_(f | gen_F n xc f) gen_prod_mu f = Cell.
    apply: eq_bigl => f; rewrite /gen_F /xc.
    apply/forallP/forallP => H i; have /implyP Hi := H i;
      apply/implyP => Hin;
      have Hij : i != j by [apply: contraTN Hin => /eqP ->; rewrite -leqNgt];
      move: (Hi Hin); by rewrite swap_at_ne.
  have := gen_cell_mass_step Hn xc.
  rewrite Hxcj HcellEq => Hstep.
  rewrite -Hstep; apply: eq_bigl => f.
  rewrite (gen_F_split Hn) Hxcj; congr (_ && _).
  rewrite /gen_F /xc; apply/forallP/forallP => H i;
    have /implyP Hi := H i; apply/implyP => Hin;
    have Hij : i != j by [apply: contraTN Hin => /eqP ->; rewrite -leqNgt];
    move: (Hi Hin); by rewrite swap_at_ne.
exact: Hswap.
Qed.

(** Conditional expectation of a free-coordinate function. *)
Lemma gen_cond_exp_free (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> C}) (g : C -> R) :
  0 < \sum_(f | gen_F n x f) gen_prod_mu f ->
  @cond_exp R _ gen_prod_mu gen_F
    (fun f => g (f (Ordinal Hn))) n x =
  \sum_(c : C) mu0 c * g c.
Proof.
move=> Hcell; rewrite /cond_exp.
set j := Ordinal Hn.
have Hnum : \sum_(f | gen_F n x f) gen_prod_mu f * g (f j) =
  (\sum_(c : C) mu0 c * g c) * \sum_(f | gen_F n x f) gen_prod_mu f.
  transitivity (\sum_(c : C) g c *
    \sum_(f | gen_F n x f && (f j == c)) gen_prod_mu f).
    rewrite (partition_big (fun f : {ffun 'I_N -> C} => f j) predT) //=.
    apply: eq_bigr => c _.
    rewrite big_distrr /=.
    apply: eq_bigr => f /andP [_ /eqP ->].
    by rewrite mulrC.
  transitivity (\sum_(c : C) (g c * mu0 c) *
    \sum_(f | gen_F n x f) gen_prod_mu f).
    apply: eq_bigr => c _; rewrite (gen_cell_mass_coord Hn x c).
    by rewrite mulrA.
  rewrite -big_distrl /=; congr (_ * _).
  by apply: eq_bigr => c _; rewrite mulrC.
rewrite Hnum.
have Hden : \sum_(f | gen_F n x f) gen_prod_mu f != 0 by rewrite gt_eqF.
by rewrite mulfK.
Qed.

(** E[gen_lr(f_n) | F_n] = 1 under the general model. *)
Lemma gen_cond_exp_lr (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> C}) :
  0 < \sum_(f | gen_F n x f) gen_prod_mu f ->
  @cond_exp R _ gen_prod_mu gen_F
    (fun f => gen_lr (f (Ordinal Hn))) n x = 1.
Proof.
move=> Hcell; rewrite (@gen_cond_exp_free n Hn x gen_lr Hcell).
exact: gen_lr_exp1.
Qed.

(** Time-varying process for the general model. *)
Definition gen_M (n : nat) (f : {ffun 'I_N -> C}) : R :=
  \prod_(i < N | (i < n)%N) gen_lr (f i).

Lemma gen_M_0 (f : {ffun 'I_N -> C}) : gen_M 0 f = 1.
Proof. by rewrite /gen_M big_pred0 // => i; rewrite ltn0. Qed.

Lemma gen_M_ge0 (n : nat) (f : {ffun 'I_N -> C}) : 0 <= gen_M n f.
Proof. by apply: prodr_ge0 => i _; exact: gen_lr_ge0. Qed.

Lemma gen_M_step (n : nat) (Hn : (n < N)%N)
    (f : {ffun 'I_N -> C}) :
  gen_M n.+1 f = gen_M n f * gen_lr (f (Ordinal Hn)).
Proof.
rewrite /gen_M (bigD1 (Ordinal Hn)) //= mulrC.
congr (_ * gen_lr _); apply: eq_bigl => i.
by rewrite ltnS -(inj_eq val_inj) /= andbC -ltn_neqAle.
Qed.

Lemma gen_M_adapted (n : nat) (x f : {ffun 'I_N -> C}) :
  gen_F n x f -> gen_M n x = gen_M n f.
Proof.
move/forallP => Hxf; apply: eq_bigr => i Hi.
by congr (gen_lr _); apply/eqP; exact: implyP (Hxf i) Hi.
Qed.

Lemma gen_M_supermartingale :
  @supermartingale R _ gen_prod_mu gen_F gen_M.
Proof.
split.
- by move=> n x y Hxy; exact: gen_M_adapted Hxy.
- move=> n x.
  case: (ltnP n N) => Hn.
  + set j := Ordinal Hn.
    rewrite /cond_exp.
    set den := \sum_(f | gen_F n x f) gen_prod_mu f.
    have Hden : 0 < den := gen_F_cell_pos n x.
    have Hnum : \sum_(f | gen_F n x f) gen_prod_mu f * gen_M n.+1 f =
      gen_M n x * \sum_(f | gen_F n x f) gen_prod_mu f * gen_lr (f j).
      rewrite mulr_sumr; apply: eq_bigr => f Hf.
      by rewrite (gen_M_step Hn) mulrCA -(gen_M_adapted Hf).
    rewrite Hnum -mulrA.
    have := @gen_cond_exp_lr n Hn x Hden.
    by rewrite /cond_exp -/den => ->; rewrite mulr1.
  + have HM : gen_M n.+1 x = gen_M n x.
      rewrite /gen_M; apply: eq_bigl => i.
      by rewrite (leq_trans (ltn_ord i) Hn)
                 (leq_trans (ltn_ord i) (leqW Hn)).
    rewrite (@cond_exp_measurable R _ gen_prod_mu gen_F
      (gen_M n.+1) n x gen_filtration).
    * by rewrite HM.
    * move=> f /forallP Hf; rewrite /gen_M; apply: eq_bigr => i _.
      by rewrite (eqP (implyP (Hf i) (leq_trans (ltn_ord i) Hn))).
    * exact: gen_F_cell_pos.
Qed.

Lemma gen_M_Exp0 : @Exp R _ gen_prod_mu (gen_M 0) <= 1.
Proof.
rewrite /Exp (eq_bigr (fun f => gen_prod_mu f)); last first.
  by move=> f _; rewrite gen_M_0 mulr1.
by rewrite gen_prod_mu_sum1.
Qed.

(** Ville's inequality for the general ballot model. *)
Lemma gen_M_ville (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R _ gen_prod_mu
    (fun f => alpha^-1 <= gen_M n f) <= alpha.
Proof.
move=> Ha0 Ha1.
apply: (ville_ineq (F := gen_F) gen_prod_mu_ge0).
- exact: gen_filtration.
- exact: gen_M_supermartingale.
- exact: gen_F_cell_pos.
- exact: gen_M_ge0.
- exact: Ha0.
- exact: Ha1.
- change (@Exp R _ gen_prod_mu (gen_M 0) <= 1).
  exact: gen_M_Exp0.
Qed.

End GeneralBallot.

(** ** Binary ballot instantiation *)

(** The binary (BRAVO) ballot model is the special case of the general
    ballot model with [C := bool], [mu0 := ballot_mu p], and
    [gen_lr := lr p].  The binary results follow by instantiation. *)

Section BinaryBallotInstantiation.

Variable R : realType.
Variable p : R.
Hypothesis Hp : 2%:R^-1 < p.
Hypothesis Hp1 : p < 1.
Variable N : nat.
Hypothesis HN : (0 < N)%N.

Lemma ballot_mu_pos : forall b : bool, 0 < ballot_mu p b.
Proof. by case; [exact: p_pos Hp | exact: q_pos Hp1]. Qed.

Definition ballot_prod_mu := @gen_prod_mu R bool (ballot_mu p) N.
Definition ballot_F := @gen_F bool N.
Definition ballot_M := @gen_M R bool (lr p) N.

Lemma ballot_M_supermartingale :
  @supermartingale R _ ballot_prod_mu ballot_F ballot_M.
Proof.
rewrite /ballot_prod_mu /ballot_F /ballot_M.
apply: gen_M_supermartingale.
- exact: ballot_mu_pos.
- exact: ballot_mu_sum1.
- exact: (@lr_expectation_1 R p Hp Hp1).
Qed.

Lemma ballot_M_ville (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R _ ballot_prod_mu
    (fun f => alpha^-1 <= ballot_M n f) <= alpha.
Proof.
move=> Ha0 Ha1.
rewrite /ballot_prod_mu /ballot_M.
apply: gen_M_ville.
- exact: ballot_mu_pos.
- exact: ballot_mu_sum1.
- by move=> b; exact: (@lr_ge0 R p Hp Hp1 b).
- exact: (@lr_expectation_1 R p Hp Hp1).
- exact: Ha0.
- exact: Ha1.
Qed.

End BinaryBallotInstantiation.

(** ** Null-hypothesis (wrong-outcome) Ville bound *)

(** The RLA risk bound requires Ville's inequality under the
    wrong-outcome (null) hypothesis: H0 says the reported winner
    did NOT truly win, modeled as the fair-coin distribution
    [p = 1/2].  The reversed likelihood ratio
    [T(b) = ballot_mu_alt(b) / ballot_mu_null(b)] is a martingale
    under H0 and Ville gives [Pr(T >= 1/alpha | H0) <= alpha].
    "Confirming the outcome" = [T >= 1/alpha], so this directly
    bounds the probability of falsely certifying a wrong outcome.

    The null model is an instance of [GeneralBallot] with
    [C := bool], [mu0 := null_mu] (fair coin), [gen_lr := rev_lr]
    (the reversed likelihood ratio). *)

Section NullVille.

Variable R : realType.
Variable p_alt : R.
Hypothesis Hp_gt_half : 2%:R^-1 < p_alt.
Hypothesis Hp_lt1 : p_alt < 1.

Definition null_mu (b : bool) : R := 2%:R^-1.

Lemma null_mu_pos (b : bool) : 0 < null_mu b.
Proof. by rewrite /null_mu invr_gt0 ltr0n. Qed.

Lemma null_mu_sum1 : \sum_(b : bool) null_mu b = 1.
Proof.
rewrite big_bool /null_mu.
by rewrite -[1 in RHS](subrK (2%:R^-1 : R)) half_complement.
Qed.

Definition rev_lr (b : bool) : R :=
  ballot_mu p_alt b / null_mu b.

Lemma rev_lr_ge0 (b : bool) : 0 <= rev_lr b.
Proof.
rewrite /rev_lr.
apply: divr_ge0.
- rewrite /ballot_mu; case: b; last by rewrite subr_ge0; exact: ltW.
  apply: ltW; apply: (lt_trans _ Hp_gt_half); rewrite invr_gt0 ltr0n; exact: isT.
- by rewrite /null_mu; apply: ltW; rewrite invr_gt0 ltr0n.
Qed.

Lemma rev_lr_exp1 : \sum_(b : bool) null_mu b * rev_lr b = 1.
Proof.
rewrite big_bool /rev_lr /=.
have Hcancel : forall b : bool,
  null_mu b * (ballot_mu p_alt b / null_mu b) = ballot_mu p_alt b.
  move=> b; rewrite mulrCA mulfV ?mulr1 //.
  by rewrite gt_eqF // null_mu_pos.
rewrite !Hcancel /ballot_mu /=.
by rewrite addrC subrK.
Qed.

Variable N : nat.
Hypothesis HN : (0 < N)%N.

Definition null_prod_mu (f : {ffun 'I_N -> bool}) : R :=
  @gen_prod_mu R bool null_mu N f.

Definition null_F := @gen_F bool N.

Definition rev_M (n : nat) (f : {ffun 'I_N -> bool}) : R :=
  @gen_M R bool rev_lr N n f.

Lemma rev_M_supermartingale :
  @supermartingale R _ null_prod_mu null_F rev_M.
Proof.
rewrite /null_prod_mu /null_F /rev_M.
apply: gen_M_supermartingale.
- exact: null_mu_pos.
- exact: null_mu_sum1.
- exact: rev_lr_exp1.
Qed.

Lemma rev_M_ge0 (n : nat) (f : {ffun 'I_N -> bool}) :
  0 <= rev_M n f.
Proof. by rewrite /rev_M; apply: prodr_ge0 => i _; exact: rev_lr_ge0. Qed.

Lemma null_prod_mu_ge0 (f : {ffun 'I_N -> bool}) : 0 <= null_prod_mu f.
Proof.
rewrite /null_prod_mu; apply: prodr_ge0 => i _.
exact: ltW (null_mu_pos _).
Qed.

Lemma null_filtration : @filtration _ null_F.
Proof. exact: (@gen_filtration bool N). Qed.

Lemma null_F_cell_pos (n : nat) (x : {ffun 'I_N -> bool}) :
  0 < \sum_(y | null_F n x y) null_prod_mu y.
Proof. exact: (@gen_F_cell_pos R bool null_mu null_mu_pos N n x). Qed.

Lemma rev_M_Exp0 : @Exp R _ null_prod_mu (rev_M 0) <= 1.
Proof.
rewrite /null_prod_mu /rev_M.
apply: gen_M_Exp0; exact: null_mu_sum1.
Qed.

(** Ville's inequality under the null (wrong-outcome) measure:
    [Pr_null(rev_M n >= 1/alpha) <= alpha].
    This is [Pr(confirming wrong outcome | H0) <= alpha]. *)
Lemma null_ville (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R _ null_prod_mu (fun f => alpha^-1 <= rev_M n f) <= alpha.
Proof.
move=> Ha0 Ha1.
rewrite /null_prod_mu /rev_M.
apply: gen_M_ville.
- exact: null_mu_pos.
- exact: null_mu_sum1.
- exact: rev_lr_ge0.
- exact: rev_lr_exp1.
- exact: Ha0.
- exact: Ha1.
Qed.

(** The per-contest false certification probability under the null is
    at most [alpha]. *)
Lemma bravo_pass_prob_bound (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  1 - @Pr R _ null_prod_mu (fun f => alpha^-1 <= rev_M n f)
  >= 1 - alpha.
Proof.
move=> Ha0 Ha1; rewrite lerD2l lerN2.
exact: null_ville Ha0 Ha1.
Qed.

End NullVille.

(** ** Closed-form end-to-end degradation *)

(** For [k] independent contests, each with per-contest Ville bound
    [Pr(confirm wrong_i | H0) <= alpha_i], the false certification
    probability for at least one wrong outcome surviving is bounded
    by [false_assurance_hetero].  The bound is tight: it equals
    [1 - prod(1 - alpha_i)] with equality. *)

Section BRAVOEndToEnd.

Variable R : realType.

Lemma bravo_end_to_end (k : nat) (alphas : 'I_k -> R) :
  (forall i, 0 < alphas i) ->
  (forall i, alphas i < 1) ->
  false_assurance_hetero alphas <=
    1 - joint_pass (fun i => 1 - alphas i).
Proof.
move=> Ha0 Ha1; apply: degradation_from_per_contest.
- by move=> i; apply/andP; split; [exact: ltW | exact: ltW].
- move=> i; apply/andP; split.
  + by rewrite subr_ge0; exact: ltW.
  + exact: lexx.
Qed.

Lemma bravo_end_to_end_tight (k : nat) (alphas : 'I_k -> R) :
  false_assurance_hetero alphas =
    1 - joint_pass (fun i => 1 - alphas i).
Proof. by rewrite /false_assurance_hetero /joint_pass. Qed.

End BRAVOEndToEnd.

(* --- Bibliography ---

   ballot_mu, lr, lr_expectation_1, lr_Exp_eq1, lr_win_lt1,
   lr_lose_gt1:
     M. Lindeman, P. B. Stark, and V. S. Yates, "BRAVO:
     ballot-polling risk-limiting audits to verify outcomes,"
     2012 Electronic Voting Technology Workshop / Workshop on
     Trustworthy Elections (EVT/WOTE '12), USENIX, 2012.
     The likelihood-ratio martingale originates in A. Wald,
     Sequential Analysis, John Wiley & Sons, New York, 1947.

   rlt_ville, ville_ineq (from ville_6.v):
     J. Ville, Étude critique de la notion de collectif,
     Gauthier-Villars, Paris, 1939.

   degradation_from_per_contest:
     Composition of the per-contest BRAVO bound with the
     multiplicative degradation theory (auditing_1.v).
     See P. B. Stark, "Risk-limiting postelection audits:
     conservative P-values from common probability inequalities,"
     IEEE Trans. Inform. Forensics Security, 4(4):1005-1014,
     2009.  DOI: 10.1109/TIFS.2009.2034190

   gen_prod_mu_sum1, gen_cell_mass:
     Product-measure normalization via bigA_distr_bigA.
     Cell mass factorization via swap_at coordinate bijection.
     Standard; see e.g. R. Durrett, Probability: Theory and
     Examples, 5th ed., Cambridge University Press, 2019.

   multiplicative_martingale_step:
     The pull-out property of conditional expectation for
     measurable factors.  Standard; see J. L. Doob,
     Stochastic Processes, Wiley, 1953, Ch. VII.
*)

Print Assumptions lr_expectation_1.
Print Assumptions degradation_from_per_contest.
Print Assumptions trivial_filtration_ok.
Print Assumptions gen_M_ville.
Print Assumptions ballot_M_ville.
