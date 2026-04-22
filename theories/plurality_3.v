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

Print Assumptions M_3_ville.
