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

(** ** Cell mass factorization *)

(** [flip_at j f]: flip coordinate [j] of [f], leaving all others unchanged.
    Used to establish the bijection between the "agree" and "disagree"
    halves of a filtration cell when splitting by a free coordinate. *)
Definition flip_at (j : 'I_N) (f : {ffun 'I_N -> bool}) : {ffun 'I_N -> bool} :=
  [ffun i => if i == j then ~~ f i else f i].

(** [flip_at] is an involution. *)
Lemma flip_at_invol (j : 'I_N) : involutive (flip_at j).
Proof.
by move=> f; apply/ffunP => i; rewrite !ffunE; case: eqP => //= _; rewrite negbK.
Qed.

(** [flip_at] is injective. *)
Lemma flip_at_inj (j : 'I_N) : injective (flip_at j).
Proof. exact: inv_inj (flip_at_invol j). Qed.

(** [flip_at] preserves coordinates other than [j]. *)
Lemma flip_at_ne (j : 'I_N) (f : {ffun 'I_N -> bool}) (i : 'I_N) :
  i != j -> (flip_at j f) i = f i.
Proof. by rewrite ffunE => /negbTE ->. Qed.

(** [flip_at] negates coordinate [j]. *)
Lemma flip_at_eq (j : 'I_N) (f : {ffun 'I_N -> bool}) :
  (flip_at j f) j = ~~ f j.
Proof. by rewrite ffunE eqxx. Qed.

(** [flip_at] preserves the [ballot_F n] equivalence class when [n <= j]:
    flipping a free coordinate does not affect the first [n] positions. *)
Lemma flip_at_ballot_F (n : nat) (j : 'I_N) (x f : {ffun 'I_N -> bool}) :
  (n <= j)%N -> ballot_F n x f -> ballot_F n x (flip_at j f).
Proof.
move=> Hnj /forallP Hxf; apply/forallP => i; apply/implyP => Hi.
have Hij : i != j.
  by apply: contraTN Hi => /eqP ->; rewrite -leqNgt.
by rewrite flip_at_ne //; exact: implyP (Hxf i) Hi.
Qed.

(** [flip_at] preserves the [ballot_F n] cell as a boolean identity. *)
Lemma flip_at_ballot_F_id (n : nat) (j : 'I_N) (x f : {ffun 'I_N -> bool}) :
  (n <= j)%N -> ballot_F n x (flip_at j f) = ballot_F n x f.
Proof.
move=> Hnj; apply/forallP/forallP => /= H i;
  have /implyP Hi := H i; apply/implyP => Hin;
  have Hij : i != j by [apply: contraTN Hin => /eqP ->; rewrite -leqNgt];
  move: (Hi Hin); by rewrite flip_at_ne.
Qed.

(** The reduced product (excluding coordinate [j]) is preserved by [flip_at j]. *)
Lemma flip_at_reduced_prod (j : 'I_N) (f : {ffun 'I_N -> bool}) :
  \prod_(i < N | i != j) ballot_mu p ((flip_at j f) i) =
  \prod_(i < N | i != j) ballot_mu p (f i).
Proof.
by apply: eq_bigr => i Hij; rewrite flip_at_ne.
Qed.

(* Prevent kernel unfolding of flip_at infrastructure. *)
Strategy 100 [flip_at].

(** Cell mass recurrence: the [n+1]-cell mass is the [n]-cell mass
    times the ballot measure at coordinate [n].

    The proof splits the [n]-cell by the value at coordinate [n]
    (which is free in the [n]-cell), factors out the ballot measure
    from each half, and uses [flip_at] to equate the reduced-product
    sums over the "agree" and "disagree" halves.  The two ballot
    measures sum to 1, collapsing the [n]-cell mass to the
    reduced-product sum, which then recombines with the [n+1]-cell. *)
Lemma ballot_F_cell_mass_step (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> bool}) :
  \sum_(f | ballot_F n.+1 x f) ballot_prod_mu f =
  ballot_mu p (x (Ordinal Hn)) *
  \sum_(f | ballot_F n x f) ballot_prod_mu f.
Proof.
set j := Ordinal Hn.
(* Reduced product: ballot_prod_mu without coordinate j *)
set rprod := fun f : {ffun 'I_N -> bool} =>
  \prod_(i < N | i != j) ballot_mu p (f i).
(* S := reduced-product sum over cell(n+1) *)
set S := \sum_(f | ballot_F n.+1 x f) rprod f.
(* Step A: cell(n+1) = ballot_mu(x j) * S *)
have HA : \sum_(f | ballot_F n.+1 x f) ballot_prod_mu f =
          ballot_mu p (x j) * S.
  rewrite /S mulr_sumr; apply: eq_bigr => f Hf.
  rewrite /ballot_prod_mu (bigD1 j) //=; congr (_ * _).
  by move: Hf; rewrite (ballot_F_split Hn) => /andP [_ /eqP ->].
(* Step B: cell(n) = S *)
suff HB : \sum_(f | ballot_F n x f) ballot_prod_mu f = S
  by rewrite HA HB.
(* Split cell(n) by f(j) using bigID *)
rewrite (bigID (fun f : {ffun _ -> _} => f j == x j)) /=.
(* Factor ballot_prod_mu in each half *)
have Hfactor : forall f : {ffun 'I_N -> bool},
  ballot_prod_mu f = ballot_mu p (f j) * rprod f.
  by move=> f; rewrite /ballot_prod_mu (bigD1 j).
(* Agree half: ballot_F n x f && f(j) == x(j)  is  cell(n+1) *)
have Hagree :
  \sum_(f | ballot_F n x f && (f j == x j)) ballot_prod_mu f =
  ballot_mu p (x j) * S.
  transitivity (\sum_(f | ballot_F n.+1 x f) ballot_prod_mu f).
    by apply: eq_bigl => f; rewrite (ballot_F_split Hn).
  exact: HA.
(* Disagree rprod-sum = S via flip_at reindex *)
have Hflip_rprod :
  \sum_(f | ballot_F n x f && (f j != x j)) rprod f = S.
  rewrite /S; symmetry.
  have Hinj : injective (flip_at j).
    by move=> a b /(congr1 (flip_at j)); rewrite !flip_at_invol.
  rewrite (reindex_inj Hinj).
  apply: eq_big => f.
  - (* Predicate: ballot_F n.+1 x (flip f) = ballot_F n x f && f(j) != x(j) *)
    rewrite (ballot_F_split Hn) flip_at_eq
            (@flip_at_ballot_F_id _ j _ _ (leqnn _)).
    by congr (_ && _); case: (f j); case: (x j).
  - (* Body: rprod(flip f) = rprod(f) *)
    by move=> _; exact: flip_at_reduced_prod.
(* Disagree half = ballot_mu(~~x j) * S *)
have Hdisagree :
  \sum_(f | ballot_F n x f && (f j != x j)) ballot_prod_mu f =
  ballot_mu p (~~ x j) * S.
  rewrite -Hflip_rprod mulr_sumr.
  apply: eq_bigr => f /andP [_ Hne].
  rewrite Hfactor; congr (ballot_mu p _ * _).
  by case: (f j) (x j) Hne => [] [].
(* Combine: cell(n) = (ballot_mu(x j) + ballot_mu(~~x j)) * S = S *)
rewrite Hagree Hdisagree -mulrDl.
suff -> : ballot_mu p (x j) + ballot_mu p (~~ x j) = 1 by rewrite mul1r.
by case: (x j); rewrite /ballot_mu /= ?addrC subrK.
Qed.

(** General cell mass formula: the sum of [ballot_prod_mu] over the
    [ballot_F n] cell of [x] equals the product of ballot measures
    at the first [n] coordinates of [x].

    At [n = 0] the product is empty (= 1) and the cell is the full space.
    At [n = N] every coordinate is fixed and the cell is the singleton [{x}].
    The general case follows by forward induction on [n] using the
    recurrence [ballot_F_cell_mass_step]. *)
Lemma ballot_F_cell_mass (n : nat) (Hn : (n <= N)%N)
    (x : {ffun 'I_N -> bool}) :
  \sum_(f : {ffun 'I_N -> bool} | ballot_F n x f) ballot_prod_mu f =
  \prod_(i < N | (i < n)%N) ballot_mu p (x i).
Proof.
elim: n Hn => [|n IH] Hn.
  rewrite big_pred0; last by move=> i; rewrite ltn0.
  exact: ballot_F_cell_mass_0.
have Hn' : (n < N)%N := Hn.
rewrite (ballot_F_cell_mass_step Hn') (IH (ltnW Hn)).
set j := Ordinal Hn'.
rewrite (bigD1 j) /=; last by [].
congr (ballot_mu p (x j) * _).
apply: eq_bigl => i.
(* Goal: (i < n.+1)%N && (i != j) = (i < n)%N *)
by rewrite ltnS -(inj_eq val_inj) /= andbC -ltn_neqAle.
Qed.

(** The sum of [ballot_prod_mu] over the cell of [ballot_F n] restricted
    to a specific value at coordinate [n] equals [ballot_mu p b] times
    the cell mass.  Proved by complementation: the agree half is
    [cell(n+1)] from [ballot_F_cell_mass_step], and the disagree half
    is the remainder. *)
Lemma ballot_F_cell_mass_coord (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> bool}) (b : bool) :
  \sum_(f | ballot_F n x f && (f (Ordinal Hn) == b)) ballot_prod_mu f =
  ballot_mu p b * \sum_(f | ballot_F n x f) ballot_prod_mu f.
Proof.
set j := Ordinal Hn.
set C := \sum_(f | ballot_F n x f) ballot_prod_mu f.
(* Split cell by f j *)
have Hsplit : C =
  \sum_(f | ballot_F n x f && (f j == x j)) ballot_prod_mu f +
  \sum_(f | ballot_F n x f && (f j != x j)) ballot_prod_mu f
  by rewrite -bigID.
(* The agree half = cell(n+1) = ballot_mu(x j) * C *)
have Hagree :
  \sum_(f | ballot_F n x f && (f j == x j)) ballot_prod_mu f =
  ballot_mu p (x j) * C.
  have HH := ballot_F_cell_mass_step Hn x.
  rewrite -/j in HH.
  rewrite -/C -HH; apply: eq_bigl => f.
  by rewrite (ballot_F_split Hn).
(* The disagree half = ballot_mu(~~x j) * C by complement *)
have Hdisagree :
  \sum_(f | ballot_F n x f && (f j != x j)) ballot_prod_mu f =
  ballot_mu p (~~ x j) * C.
  have : C - ballot_mu p (x j) * C =
    ballot_mu p (~~ x j) * C.
    rewrite -mulrBl; congr (_ * C).
    by case: (x j); rewrite /ballot_mu //= opprB addrCA subrr addr0.
  by rewrite -Hagree -Hsplit addrK.
(* Case split on b *)
case Hb: (b == x j).
- by move/eqP: Hb => ->; exact: Hagree.
- have -> : b = ~~ x j by case: b (x j) Hb => [] [].
  exact: Hdisagree.
Qed.

(** Conditional expectation of any function [g] applied to a free
    coordinate [n_ord] given [ballot_F n] equals the unconditional
    expectation [sum_b ballot_mu b * g b].  The product measure
    structure makes free coordinates conditionally independent
    of the fixed ones. *)
Lemma ballot_F_cond_exp_free (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> bool}) (g : bool -> R) :
  0 < \sum_(f | ballot_F n x f) ballot_prod_mu f ->
  @cond_exp R _ ballot_prod_mu ballot_F
    (fun f => g (f (Ordinal Hn))) n x =
  \sum_(b : bool) ballot_mu p b * g b.
Proof.
move=> Hcell; rewrite /cond_exp.
set j := Ordinal Hn.
(* Numerator = sum_b [ballot_mu b * g b] * cell_mass *)
have Hnum : \sum_(f | ballot_F n x f) ballot_prod_mu f * g (f j) =
            (\sum_(b : bool) ballot_mu p b * g b) *
            \sum_(f | ballot_F n x f) ballot_prod_mu f.
  rewrite (bigID (fun f : {ffun _ -> _} => f j)) /=.
  have Htrue : \sum_(f | ballot_F n x f && f j)
    ballot_prod_mu f * g (f j) =
    ballot_mu p true * g true *
    \sum_(f | ballot_F n x f) ballot_prod_mu f.
    under eq_bigr do rewrite [_ && f j]andbC => /andP [/eqP -> _].
    rewrite -mulr_sumr -(ballot_F_cell_mass_coord Hn x true).
    by apply: eq_bigl => f; rewrite [_ && f j]andbC.
  have Hfalse : \sum_(f | ballot_F n x f && ~~ f j)
    ballot_prod_mu f * g (f j) =
    ballot_mu p false * g false *
    \sum_(f | ballot_F n x f) ballot_prod_mu f.
    under eq_bigr do rewrite [_ && ~~ f j]andbC => /andP [Hnf _].
    have -> : forall f0, ~~ f0 j -> g (f0 j) = g false
      by move=> f0; case: (f0 j).
    rewrite -mulr_sumr -(ballot_F_cell_mass_coord Hn x false).
    apply: eq_bigl => f; rewrite [_ && ~~ f j]andbC.
    congr (_ && _); by case: (f j).
  rewrite Htrue Hfalse big_bool /= -mulrDl.
  done.
rewrite Hnum mulrA mulfK //; last exact: gt_eqF.
done.
Qed.

(** Conditional expectation of [lr] at a free coordinate equals 1. *)
Lemma ballot_F_cond_exp_lr (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> bool}) :
  0 < \sum_(f | ballot_F n x f) ballot_prod_mu f ->
  @cond_exp R _ ballot_prod_mu ballot_F
    (fun f => lr p (f (Ordinal Hn))) n x = 1.
Proof.
move=> Hcell; rewrite (ballot_F_cond_exp_free Hn x (lr p) Hcell).
exact: lr_expectation_1.
Qed.

(** ** Time-varying product likelihood ratio *)

(** [ballot_M n f]: the product likelihood ratio at step [n], using
    only the first [n] coordinates of [f].  Defined as a filtered
    product to avoid dependent-type proof terms in the time index. *)
Definition ballot_M (n : nat) (f : {ffun 'I_N -> bool}) : R :=
  \prod_(i < N | (i < n)%N) lr p (f i).

Lemma ballot_M_0 (f : {ffun 'I_N -> bool}) : ballot_M 0 f = 1.
Proof. by rewrite /ballot_M big_pred0 // => i; rewrite ltn0. Qed.

Lemma ballot_M_ge0 (n : nat) (f : {ffun 'I_N -> bool}) :
  0 <= ballot_M n f.
Proof. by apply: prodr_ge0 => i _; exact: lr_ge0. Qed.

Lemma ballot_M_step (n : nat) (Hn : (n < N)%N)
    (f : {ffun 'I_N -> bool}) :
  ballot_M n.+1 f = ballot_M n f * lr p (f (Ordinal Hn)).
Proof.
rewrite /ballot_M (bigD1 (Ordinal Hn)) //=.
congr (lr p _ * _); apply: eq_bigl => i.
by rewrite ltnS -(inj_eq val_inj) /= andbC -ltn_neqAle.
Qed.

Lemma ballot_M_adapted (n : nat) (x f : {ffun 'I_N -> bool}) :
  ballot_F n x f -> ballot_M n x = ballot_M n f.
Proof.
move/forallP => Hxf; apply: eq_bigr => i /andP [_ Hi].
by congr (lr p _); apply/eqP; exact: implyP (Hxf i) Hi.
Qed.

(** ** Supermartingale property *)

Lemma ballot_M_supermartingale :
  @supermartingale R _ ballot_prod_mu ballot_F ballot_M.
Proof.
split.
- by move=> n x y Hxy; exact: ballot_M_adapted Hxy.
- move=> n x.
  case: (ltnP n N) => Hn.
  + (* n < N: factor ballot_M(n+1) = ballot_M(n) * lr(f_n) *)
    set j := Ordinal Hn.
    rewrite /cond_exp.
    set den := \sum_(f | ballot_F n x f) ballot_prod_mu f.
    have Hden : 0 < den := ballot_F_cell_pos n x.
    (* Rewrite numerator: replace M(n+1) with M(n) * lr *)
    have Hnum : \sum_(f | ballot_F n x f) ballot_prod_mu f * ballot_M n.+1 f =
      ballot_M n x * \sum_(f | ballot_F n x f) ballot_prod_mu f * lr p (f j).
      rewrite mulr_sumr; apply: eq_bigr => f Hf.
      by rewrite (ballot_M_step Hn) mulrA -(ballot_M_adapted Hf).
    rewrite Hnum mulrA mulfK; last exact: gt_eqF.
    (* The remaining sum / den is cond_exp of lr = 1 *)
    have := ballot_F_cond_exp_lr Hn x Hden.
    by rewrite /cond_exp -/den => ->; rewrite mulr1.
  + (* n >= N: ballot_M is constant *)
    rewrite (@cond_exp_measurable R _ ballot_prod_mu ballot_F
      (ballot_M n.+1) n x ballot_filtration) //.
    * move=> f Hf; rewrite /ballot_M; apply: eq_bigl => i.
      by rewrite (ltn_leq_trans (ltn_ord i) Hn)
                 (ltn_leq_trans (ltn_ord i) (leqW Hn)).
    * exact: ballot_F_cell_pos.
Qed.

Lemma ballot_M_Exp0 : @Exp R _ ballot_prod_mu (ballot_M 0) <= 1.
Proof.
rewrite /Exp (eq_bigr (fun f => ballot_prod_mu f)); last first.
  by move=> f _; rewrite ballot_M_0 mulr1.
by rewrite ballot_prod_mu_sum1.
Qed.

(** Ville's inequality for the product likelihood ratio on the ballot
    product space. *)
Lemma ballot_M_ville (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R _ ballot_prod_mu
    (fun f => alpha^-1 <= ballot_M n f) <= alpha.
Proof.
move=> Ha0 Ha1.
exact: (@ville_ineq R _ ballot_prod_mu ballot_F ballot_M alpha n
  ballot_filtration ballot_M_supermartingale
  ballot_F_cell_pos (fun k x => ballot_M_ge0 k x)
  Ha0 Ha1 ballot_M_Exp0).
Qed.

End BallotProductSpace.

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

(** ** General ballot model (multi-candidate) *)

(** Generalizes the binary ballot model from [bool] to an arbitrary
    [finType].  The product measure, natural filtration, cell mass
    factorization, and supermartingale machinery carry over with
    [swap_at] replacing [flip_at]. *)

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
case: eqP => [->|//].
by case: eqP => [->|]; [rewrite eqxx; case: eqP |
  case: eqP => [->|//]; rewrite eqxx].
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
Proof. by move=> ->; rewrite ffunE eqxx eqxx. Qed.

Lemma swap_at_eq_c2 (j : 'I_N) (c1 c2 : C)
    (f : {ffun 'I_N -> C}) :
  f j = c2 -> (swap_at j c1 c2 f) j = c1.
Proof.
move=> ->; rewrite ffunE eqxx.
by case: eqP => [->|_]; rewrite eqxx.
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
set rprod := fun f : {ffun 'I_N -> C} =>
  \prod_(i < N | i != j) mu0 (f i).
set S := \sum_(f | gen_F n.+1 x f) rprod f.
(* Step A: cell(n+1) = mu0(x j) * S *)
have HA : \sum_(f | gen_F n.+1 x f) gen_prod_mu f =
          mu0 (x j) * S.
  rewrite /S mulr_sumr; apply: eq_bigr => f Hf.
  rewrite /gen_prod_mu (bigD1 j) //=; congr (_ * _).
  by move: Hf; rewrite (gen_F_split Hn) => /andP [_ /eqP ->].
(* Step B: cell(n) = S *)
suff HB : \sum_(f | gen_F n x f) gen_prod_mu f = S
  by rewrite HA HB.
rewrite (bigID (fun f : {ffun _ -> _} => f j == x j)) /=.
have Hfactor : forall f : {ffun 'I_N -> C},
  gen_prod_mu f = mu0 (f j) * rprod f.
  by move=> f; rewrite /gen_prod_mu (bigD1 j).
(* Agree half *)
have Hagree :
  \sum_(f | gen_F n x f && (f j == x j)) gen_prod_mu f =
  mu0 (x j) * S.
  transitivity (\sum_(f | gen_F n.+1 x f) gen_prod_mu f).
    by apply: eq_bigl => f; rewrite (gen_F_split Hn).
  exact: HA.
(* Disagree rprod-sum = S via swap_at reindex *)
have Hswap_rprod :
  \sum_(f | gen_F n x f && (f j != x j)) rprod f = S.
  rewrite /S; symmetry.
  rewrite (reindex_inj (swap_at_inj j (x j))).
  apply: eq_big => f.
  - rewrite (gen_F_split Hn) (swap_at_gen_F _ (leqnn _)).
    congr (_ && _); rewrite ffunE eqxx.
    case: eqP => [->|Hne]; first by rewrite eqxx.
    by case: eqP => //= ->; rewrite eqxx.
  - by move=> _; exact: swap_at_reduced_prod.
(* Disagree half *)
have Hdisagree :
  \sum_(f | gen_F n x f && (f j != x j)) gen_prod_mu f =
  (1 - mu0 (x j)) * S.
  rewrite -Hswap_rprod mulrBl mul1r -Hagree.
  rewrite [X in X - _](bigID (fun f : {ffun _ -> _} => f j == x j)) /=.
  by rewrite addrK.
rewrite Hagree Hdisagree -mulrDl addrCA subrr addr0 mul1r.
Qed.

(** General cell mass formula. *)
Lemma gen_cell_mass (n : nat) (Hn : (n <= N)%N)
    (x : {ffun 'I_N -> C}) :
  \sum_(f : {ffun 'I_N -> C} | gen_F n x f) gen_prod_mu f =
  \prod_(i < N | (i < n)%N) mu0 (x i).
Proof.
elim: n Hn => [|n IH] Hn.
  rewrite big_pred0; last by move=> i; rewrite ltn0.
  have -> : \sum_(f | gen_F 0 x f) gen_prod_mu f =
            \sum_f gen_prod_mu f.
    by apply: eq_bigl => f; apply/forallP => i; rewrite ltn0.
  exact: gen_prod_mu_sum1.
rewrite (gen_cell_mass_step Hn) (IH (ltnW Hn)).
set j := Ordinal (n:=N) Hn.
rewrite (bigD1 j) /=; last by [].
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
  rewrite mulr_sumr exchange_big /=.
  apply: eq_bigr => c _.
  rewrite -mulr_sumr -(gen_cell_mass_coord Hn x c).
  rewrite mulr_sumr; apply: eq_bigr => f /andP [_ /eqP ->].
  done.
rewrite Hnum mulrA mulfK //; last exact: gt_eqF.
done.
Qed.

(** E[gen_lr(f_n) | F_n] = 1 under the general model. *)
Lemma gen_cond_exp_lr (n : nat) (Hn : (n < N)%N)
    (x : {ffun 'I_N -> C}) :
  0 < \sum_(f | gen_F n x f) gen_prod_mu f ->
  @cond_exp R _ gen_prod_mu gen_F
    (fun f => gen_lr (f (Ordinal Hn))) n x = 1.
Proof.
move=> Hcell; rewrite (gen_cond_exp_free Hn x gen_lr Hcell).
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
rewrite /gen_M (bigD1 (Ordinal Hn)) //=.
congr (gen_lr _ * _); apply: eq_bigl => i.
by rewrite ltnS -(inj_eq val_inj) /= andbC -ltn_neqAle.
Qed.

Lemma gen_M_adapted (n : nat) (x f : {ffun 'I_N -> C}) :
  gen_F n x f -> gen_M n x = gen_M n f.
Proof.
move/forallP => Hxf; apply: eq_bigr => i /andP [_ Hi].
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
      by rewrite (gen_M_step Hn) mulrA -(gen_M_adapted Hf).
    rewrite Hnum mulrA mulfK; last exact: gt_eqF.
    have := gen_cond_exp_lr Hn x Hden.
    by rewrite /cond_exp -/den => ->; rewrite mulr1.
  + rewrite (@cond_exp_measurable R _ gen_prod_mu gen_F
      (gen_M n.+1) n x gen_filtration) //.
    * move=> f Hf; rewrite /gen_M; apply: eq_bigl => i.
      by rewrite (ltn_leq_trans (ltn_ord i) Hn)
                 (ltn_leq_trans (ltn_ord i) (leqW Hn)).
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
exact: (@ville_ineq R _ gen_prod_mu gen_F gen_M alpha n
  gen_filtration gen_M_supermartingale
  gen_F_cell_pos (fun k x => gen_M_ge0 k x)
  Ha0 Ha1 gen_M_Exp0).
Qed.

End GeneralBallot.

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
