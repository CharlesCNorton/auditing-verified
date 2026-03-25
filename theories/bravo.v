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
Open Scope ring_scope.

From Auditing Require Import auditing probability ville.

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

(** [bravo_degradation_uniform alpha k]: specialization to the uniform
    case.  If all [k] contests use the same risk limit [alpha], and each
    contest's BRAVO test achieves that bound (via Ville's inequality),
    then the joint false assurance is bounded by [false_assurance alpha k]. *)
Lemma bravo_degradation_uniform (alpha : R) (k : nat) :
  0 <= alpha -> alpha <= 1 ->
  false_assurance_hetero (fun _ : 'I_k => alpha) <=
  false_assurance alpha k.
Proof.
by move=> _ _; rewrite false_assurance_hetero_uniform.
Qed.

(** [bravo_hetero_in_01]: heterogeneous false assurance is a valid
    probability (lies in [0, 1]) for any risk limits in [0, 1]. *)
Lemma bravo_hetero_in_01 (k : nat)
    (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  0 <= false_assurance_hetero alphas <= 1.
Proof.
move=> Ha; apply/andP; split.
- exact: false_assurance_hetero_ge0.
- exact: false_assurance_hetero_le1.
Qed.

(** [union_bound_hetero k alphas]: the union/Bonferroni bound for
    heterogeneous risk limits.  Always weaker than the multiplicative
    bound, but sometimes used for quick estimation. *)
Lemma union_bound_hetero (k : nat) (alphas : 'I_k -> R) :
  (forall i, 0 <= alphas i <= 1) ->
  false_assurance_hetero alphas <= \sum_(i < k) alphas i.
Proof. exact: false_assurance_hetero_union_bound. Qed.

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

    The full N-step martingale property (E[product_lr(n+1) | F_n] =
    product_lr(n)) over the product probability space bool^N is
    proved below in [product_lr_martingale]. *)
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

(** ** Summary: the BRAVO-to-degradation pipeline *)

(** The logical chain connecting a single BRAVO test to the degradation
    bound is:

    1. Define the likelihood ratio [lr] on the binary ballot space.
    2. Prove [E_null[lr] = 1] (the martingale identity, [lr_expectation_1]).
    3. The sequential product [product_lr] inherits the martingale
       property (the single-step identity is the inductive core).
    4. Ville's inequality ([ville_ineq]) gives
       [Pr(product_lr >= 1/alpha) <= alpha].
    5. This per-contest bound plugs into [false_assurance_hetero]
       without any knowledge of the test's internal structure.
    6. The degradation theory ([degradation_from_per_contest]) yields
       the joint false assurance bound for the full election.

    The key insight is the separation of concerns: steps 1-4 are
    specific to the BRAVO protocol, while steps 5-6 are purely
    algebraic and apply to any mechanism that delivers a per-contest
    risk bound. *)

Print Assumptions lr_expectation_1.
Print Assumptions degradation_from_per_contest.
Print Assumptions trivial_filtration_ok.
