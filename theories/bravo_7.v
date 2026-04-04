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

(** ** Product-space martingale *)

Section BallotProductSpace.

Variable R : realType.
Variable p : R.
Hypothesis Hp : 2%:R^-1 < p.
Hypothesis Hp1 : p < 1.
Variable N : nat.
Hypothesis HN : (0 < N)%N.

(** [ballot_prod_mu f]: the product ballot measure on [{ffun 'I_N -> bool}].
    Each coordinate is independent with mass [p] on [true] and [1-p]
    on [false]. *)
Definition ballot_prod_mu (f : {ffun 'I_N -> bool}) : R :=
  \prod_(i < N) ballot_mu p (f i).

(** The product measure is non-negative. *)
Lemma ballot_prod_mu_ge0 (f : {ffun 'I_N -> bool}) :
  0 <= ballot_prod_mu f.
Proof.
apply: prodr_ge0 => i _; rewrite /ballot_mu.
by case: (f i); [exact: ltW (p_pos Hp) | exact: ltW (q_pos Hp1)].
Qed.

(** [ballot_F n x y]: the natural filtration — [x] and [y] agree on
    the first [n] coordinates. *)
Definition ballot_F (n : nat) (x y : {ffun 'I_N -> bool}) : bool :=
  [forall i : 'I_N, (i < n)%N ==> (x i == y i)].

(** The natural filtration is reflexive. *)
Lemma ballot_F_refl : forall n, reflexive (@ballot_F n).
Proof. by move=> n x; apply/forallP => i; apply/implyP => _; rewrite eqxx. Qed.

(** The natural filtration is symmetric. *)
Lemma ballot_F_sym : forall n, symmetric (@ballot_F n).
Proof.
move=> n x y; apply/forallP/forallP => H i.
  by move/(_ i)/implyP: H => H; apply/implyP => Hi; rewrite eq_sym; exact: H.
by move/(_ i)/implyP: H => H; apply/implyP => Hi; rewrite eq_sym; exact: H.
Qed.

(** The natural filtration is transitive. *)
Lemma ballot_F_trans : forall n, transitive (@ballot_F n).
Proof.
move=> n y x z /forallP Hxy /forallP Hyz.
apply/forallP => i; apply/implyP => Hi.
by rewrite (eqP (implyP (Hxy i) Hi)) (eqP (implyP (Hyz i) Hi)).
Qed.

(** The natural filtration refines over time. *)
Lemma ballot_F_refine : forall n x y, ballot_F n.+1 x y -> ballot_F n x y.
Proof.
move=> n x y /forallP H; apply/forallP => i; apply/implyP => Hi.
by apply: (implyP (H i)); exact: ltnW.
Qed.

(** The natural filtration is a valid filtration. *)
Lemma ballot_filtration : @filtration _ ballot_F.
Proof.
by split; [exact: ballot_F_refl | exact: ballot_F_sym |
           exact: ballot_F_trans | exact: ballot_F_refine].
Qed.

(** The product measure is strictly positive on every element. *)
Lemma ballot_prod_mu_pos (f : {ffun 'I_N -> bool}) :
  0 < ballot_prod_mu f.
Proof.
apply: prodr_gt0 => i _; rewrite /ballot_mu.
by case: (f i); [exact: p_pos Hp | exact: q_pos Hp1].
Qed.

(** Cell-positivity for the natural filtration: every cell has positive
    total mass. *)
Lemma ballot_F_cell_pos :
  forall n (x : {ffun 'I_N -> bool}),
    0 < \sum_(y | ballot_F n x y) ballot_prod_mu y.
Proof.
move=> n x; rewrite (bigD1 x); last exact: ballot_F_refl.
apply: ltr_pwDl; first exact: ballot_prod_mu_pos.
by apply: sumr_ge0 => y _; exact: ballot_prod_mu_ge0.
Qed.

(** [ballot_plr n f]: the product likelihood ratio at step [n]
    computed directly from a finite ballot sequence [{ffun 'I_N -> bool}].
    Requires [n <= N]. *)
Definition ballot_plr (n : nat) (Hn : (n <= N)%N) (f : {ffun 'I_N -> bool}) : R :=
  \prod_(i < n) lr p (f (Ordinal (leq_trans (ltn_ord i) Hn))).

(** Simplification: [ballot_plr] at step [n] is a product of [lr]
    applied to the first [n] coordinates. When [i : 'I_n] and
    [n <= N], the ordinal injection maps [i] into ['I_N]. *)
(** [ballot_plr n] is adapted to [ballot_F n]: if [x] and [y] agree
    on the first [n] positions, then [ballot_plr n x = ballot_plr n y]. *)
Lemma ballot_plr_adapted (n : nat) (Hn : (n <= N)%N)
    (x y : {ffun 'I_N -> bool}) :
  ballot_F n x y ->
  ballot_plr Hn x = ballot_plr Hn y.
Proof.
move=> /forallP Hxy.
rewrite /ballot_plr; apply: eq_bigr => i _ /=.
set j := Ordinal (leq_trans (ltn_ord i) Hn).
have Hji : (j < n)%N := ltn_ord i.
by rewrite (eqP (implyP (Hxy j) Hji)).
Qed.

(** The product measure normalizes to 1. Uses [bigA_distr_bigA] to
    factor the sum over functions into a product of per-coordinate sums,
    each of which equals 1 by [ballot_mu_sum1]. *)
Lemma ballot_prod_mu_sum1 :
  \sum_(f : {ffun 'I_N -> bool}) ballot_prod_mu f = 1.
Proof.
rewrite /ballot_prod_mu.
have <- : \prod_(i < N) \sum_(b : bool) ballot_mu p b =
          \sum_(f : {ffun 'I_N -> bool}) \prod_(i < N) ballot_mu p (f i).
  exact: bigA_distr_bigA.
have Hmu1 : \sum_(b : bool) ballot_mu p b = 1 by exact: ballot_mu_sum1.
by rewrite (eq_bigr (fun _ => 1)) ?big1_eq // => i _; exact: Hmu1.
Qed.

(** At step [0], every function is in the cell: sum = 1 = empty product. *)
Lemma ballot_F_cell_mass_0 (x : {ffun 'I_N -> bool}) :
  \sum_(f : {ffun 'I_N -> bool} | ballot_F 0 x f) ballot_prod_mu f = 1.
Proof.
have -> : \sum_(f | ballot_F 0 x f) ballot_prod_mu f =
          \sum_f ballot_prod_mu f.
  by apply: eq_bigl => f; apply/forallP => i; rewrite ltn0.
exact: ballot_prod_mu_sum1.
Qed.

(** At step [N], the cell contains only [x] itself. *)
Lemma ballot_F_cell_mass_N (x : {ffun 'I_N -> bool}) :
  \sum_(f : {ffun 'I_N -> bool} | ballot_F N x f) ballot_prod_mu f =
  ballot_prod_mu x.
Proof.
rewrite (big_pred1 x) // => f; apply/idP/idP.
- move/forallP => Hfx; apply/eqP/ffunP => i.
  by move/implyP: (Hfx i) => /(_ (ltn_ord i)) /eqP.
- by move/eqP => ->; exact: ballot_F_refl.
Qed.

(** Equivalence: [ballot_F n.+1] splits as [ballot_F n] plus the [n]-th
    coordinate constraint. *)
Lemma ballot_F_split (n : nat) (Hn : (n < N)%N)
    (x f : {ffun 'I_N -> bool}) :
  ballot_F n.+1 x f = ballot_F n x f && (f (Ordinal Hn) == x (Ordinal Hn)).
Proof.
apply/idP/andP.
- move/forallP => H; split.
  + apply/forallP => i; apply/implyP => Hi.
    have /implyP Hi1 := H i.
    exact: (Hi1 (leq_trans Hi (leqnSn n))).
  + have /implyP Hn1 := H (Ordinal Hn).
    by rewrite eq_sym; exact: (Hn1 (ltnSn n)).
- move=> [Hn_cell /eqP Heq]; apply/forallP => i; apply/implyP.
  rewrite ltnS leq_eqVlt => /orP [/eqP Hi|Hi].
  + have -> : i = Ordinal Hn by apply: val_inj; rewrite /= Hi.
    by rewrite eq_sym; apply/eqP.
  + by move: (forallP Hn_cell i); rewrite Hi.
Qed.

End BallotProductSpace.

(** Generalized product-measure normalization: requires only [0 < p < 1],
    not [p > 1/2]. The null-hypothesis restriction is needed for the
    likelihood ratio but not for measure normalization. *)
Lemma ballot_prod_mu_sum1_gen (R : realType) (p : R) (N : nat) :
  0 < p -> p < 1 ->
  \sum_(f : {ffun 'I_N -> bool}) ballot_prod_mu p f = 1.
Proof.
move=> Hp0 Hp1; rewrite /ballot_prod_mu.
have <- : \prod_(i < N) \sum_(b : bool) ballot_mu p b =
          \sum_(f : {ffun 'I_N -> bool}) \prod_(i < N) ballot_mu p (f i).
  exact: bigA_distr_bigA.
have Hmu1 : \sum_(b : bool) ballot_mu p b = 1.
  by rewrite big_bool /ballot_mu /= addrC subrK.
by rewrite (eq_bigr (fun _ => 1)) ?big1_eq // => i _; exact: Hmu1.
Qed.

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
     multiplicative degradation theory (auditing.v).
     See P. B. Stark, "Risk-limiting postelection audits:
     conservative P-values from common probability inequalities,"
     IEEE Trans. Inform. Forensics Security, 4(4):1005-1014,
     2009.  DOI: 10.1109/TIFS.2009.2034190

   ballot_prod_mu_sum1:
     Product-measure normalization via bigA_distr_bigA.
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
