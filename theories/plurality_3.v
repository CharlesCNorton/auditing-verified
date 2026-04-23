(******************************************************************************)
(*                                                                            *)
(*     Three-candidate plurality null Ville bound                             *)
(*                                                                            *)
(*     Concrete instantiation of the general ballot model from bravo_7.v at   *)
(*     [C := 'I_3].  Exercises [gen_cell_mass_step], [gen_cond_exp_lr], and   *)
(*     the supermartingale chain on a non-binary fintype.                     *)
(*                                                                            *)
(*     The null distribution [mu3] and likelihood ratio [lr3] are abstract;   *)
(*     the file specializes the type [C] to ['I_3] and shows that             *)
(*     [gen_M_ville] fires at that specialization.                            *)
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

From Auditing Require Import auditing_1 probability_4 ville_6 bravo_7.

Section Plurality3.

Variable R : realType.

(** Null distribution on three candidates. *)
Variable mu3 : 'I_3 -> R.
Hypothesis mu3_pos : forall c : 'I_3, 0 < mu3 c.
Hypothesis mu3_sum1 : \sum_(c : 'I_3) mu3 c = 1.

(** Likelihood ratio on three candidates. *)
Variable lr3 : 'I_3 -> R.
Hypothesis lr3_ge0 : forall c : 'I_3, 0 <= lr3 c.
Hypothesis lr3_exp1 : \sum_(c : 'I_3) mu3 c * lr3 c = 1.

Variable N : nat.
Hypothesis HN : (0 < N)%N.

(** Three-candidate product space, filtration, and time-varying martingale. *)
Definition prod_mu3 := @gen_prod_mu R 'I_3 mu3 N.
Definition F_3 := @gen_F 'I_3 N.
Definition M_3 := @gen_M R 'I_3 lr3 N.

(** Ville's inequality on the three-candidate product space. *)
Lemma M_3_ville (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R {ffun 'I_N -> 'I_3} prod_mu3
    (fun f => alpha^-1 <= M_3 n f) <= alpha.
Proof.
move=> Ha0 Ha1.
rewrite /prod_mu3 /M_3.
apply: gen_M_ville.
- exact: mu3_pos.
- exact: mu3_sum1.
- exact: lr3_ge0.
- exact: lr3_exp1.
- exact: Ha0.
- exact: Ha1.
Qed.

End Plurality3.

(** ** Concrete three-candidate instance *)

(** Uniform null, mass-1-at-candidate-0 alternative, reversed likelihood
    ratio [lr3 c = 3 * mu_alt c].  [E[lr3 | mu3] = sum mu_alt = 1]. *)

Section Plurality3Concrete.

Variable R : realType.

Definition mu3_uniform (c : 'I_3) : R := 3%:R^-1.

Definition mu_alt_3 (c : 'I_3) : R :=
  if val c == 0%N then 1 else 0.

Definition lr3_concrete (c : 'I_3) : R := 3%:R * mu_alt_3 c.

Lemma mu3_uniform_pos (c : 'I_3) : 0 < mu3_uniform c.
Proof. by rewrite /mu3_uniform invr_gt0 ltr0n. Qed.

Lemma sum_const_ord3 (a : R) : \sum_(i < 3) a = a *+ 3.
Proof.
have H : forall n : nat, \sum_(i < n) a = a *+ n.
  elim=> [|n IH]; first by rewrite big_ord0.
  by rewrite big_ord_recr /= IH -mulrSr.
exact: H.
Qed.

Lemma three_ring : (3%:R : R) = 1 + 1 + 1.
Proof.
by rewrite -(natr1 2) -(natr1 1) -(natr1 0) /= add0r.
Qed.

Lemma mu3_uniform_sum1 : \sum_(c : 'I_3) mu3_uniform c = 1.
Proof.
rewrite /mu3_uniform 3!big_ord_recl big_ord0 addr0 /=.
have H3 : (3%:R : R) != 0 by rewrite pnatr_eq0.
apply: (mulIf H3).
by rewrite mul1r !mulrDl !mulVf.
Qed.

Lemma mu_alt_3_ge0 (c : 'I_3) : 0 <= mu_alt_3 c.
Proof. by rewrite /mu_alt_3; case: ifP. Qed.

Lemma mu_alt_3_sum1 : \sum_(c : 'I_3) mu_alt_3 c = 1.
Proof. by rewrite 3!big_ord_recl big_ord0 addr0 /mu_alt_3 /= !addr0. Qed.

Lemma lr3_concrete_ge0 (c : 'I_3) : 0 <= lr3_concrete c.
Proof.
rewrite /lr3_concrete; apply: mulr_ge0; first by rewrite ler0n.
exact: mu_alt_3_ge0.
Qed.

Lemma lr3_concrete_exp1 :
  \sum_(c : 'I_3) mu3_uniform c * lr3_concrete c = 1.
Proof.
rewrite /mu3_uniform /lr3_concrete.
under eq_bigr do rewrite mulrA mulVf ?pnatr_eq0 // mul1r.
exact: mu_alt_3_sum1.
Qed.

Variable N : nat.
Hypothesis HN : (0 < N)%N.

Lemma plurality3_concrete_ville (alpha : R) (n : nat) :
  0 < alpha -> alpha < 1 ->
  @Pr R {ffun 'I_N -> 'I_3} (@gen_prod_mu R _ mu3_uniform N)
    (fun f => alpha^-1 <= @gen_M R _ lr3_concrete N n f) <= alpha.
Proof.
move=> Ha0 Ha1.
apply: M_3_ville; try exact: HN.
- exact: mu3_uniform_pos.
- exact: mu3_uniform_sum1.
- exact: lr3_concrete_ge0.
- exact: lr3_concrete_exp1.
- exact: Ha0.
- exact: Ha1.
Qed.

End Plurality3Concrete.

Print Assumptions M_3_ville.
Print Assumptions plurality3_concrete_ville.
