(******************************************************************************)
(*                                                                            *)
(*     Continuity and differentiability of false assurance functions          *)
(*                                                                            *)
(*     Separated from auditing_1.v to isolate MathComp Analysis topology       *)
(*     imports from Stdlib scope conflicts.                                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import realfun num_topology topology normedtype derive.

Import numFieldTopology.Exports.
Import Order.Theory GRing.Theory Num.Theory.
Open Scope ring_scope.

(* Import auditing definitions *)
From Auditing Require Import auditing_1.

Section ContinuityAndSmoothness.
Variable R : realType.

(** [false_assurance] is continuous in [alpha] for each fixed [k]. *)
Lemma false_assurance_continuous_alpha (k : nat) :
  continuous (false_assurance (R:=R) ^~ k).
Proof.
move=> x; rewrite /false_assurance.
by apply: (@cvgB _ R^o); [exact: cvg_cst|
  apply: (@continuous_comp _ _ _ (fun x : R => 1 - x) (fun x => x ^+ k));
  [by apply: (@cvgB _ R^o); [exact: cvg_cst|exact: cvg_id]|
   exact: exprn_continuous]].
Qed.

(** The coordinate slice [t -> F_hetero(c with c_j = t)] is continuous. *)
Lemma false_assurance_hetero_continuous_coord (k : nat)
    (c : 'I_k -> R) (j : 'I_k) :
  continuous (fun t : R^o =>
    @false_assurance_hetero R k (fun i => if i == j then t else c i)).
Proof.
set C := \prod_(i < k | i != j) (1 - c i).
suff -> : (fun t : R^o =>
    @false_assurance_hetero R k (fun i => if i == j then t else c i)) =
  (fun t : R^o => 1 - (1 - t) * C : R^o).
  move=> t; apply: (@cvgB _ R^o); first exact: cvg_cst.
  apply: cvgM; last exact: cvg_cst.
  by apply: (@cvgB _ R^o); [exact: cvg_cst|exact: cvg_id].
apply: boolp.funext => t; rewrite /false_assurance_hetero (bigD1 j) //= eqxx.
congr (1 - _ * _).
by apply: eq_bigr => i Hi; rewrite (negbTE Hi).
Qed.

(** The coordinate slice [t -> F_hetero(c with c_j = t)] is affine,
    hence derivable — its derivative is the complementary product
    [C = prod_(i != j) (1 - c_i)], making the function C-infinity. *)
Lemma false_assurance_hetero_derivable_coord (k : nat)
    (c : 'I_k -> R) (j : 'I_k) (t : R^o) :
  derivable (fun t : R^o =>
    @false_assurance_hetero R k (fun i => if i == j then t else c i) : R^o) t 1.
Proof.
set C := \prod_(i < k | i != j) (1 - c i).
suff -> : (fun t : R^o =>
    @false_assurance_hetero R k (fun i => if i == j then t else c i) : R^o) =
  (fun t : R^o => 1 - (1 - t) * C : R^o).
  apply: derivableB; first exact: derivable_cst.
  apply: derivableM; last exact: derivable_cst.
  by apply: derivableB; [exact: derivable_cst | exact: derivable_id].
apply: boolp.funext => t'; rewrite /false_assurance_hetero (bigD1 j) //= eqxx.
congr (1 - _ * _).
by apply: eq_bigr => i Hi; rewrite (negbTE Hi).
Qed.

(** [false_assurance_hetero] is affine in each coordinate separately:
    as a function of the single variable [t] (with all other
    coordinates held fixed), it equals [a + t * b] where [a] and [b]
    depend only on the other coordinates.  Since affine functions are
    C-infinity, this gives smoothness along every coordinate axis. *)
Lemma false_assurance_hetero_coord_affine (k : nat)
    (c : 'I_k -> R) (j : 'I_k) :
  exists a b : R,
    (fun t : R^o =>
       @false_assurance_hetero R k (fun i => if i == j then t else c i)
       : R^o) =
    (fun t : R^o => a + t * b : R^o).
Proof.
set C := \prod_(i < k | i != j) (1 - c i).
exists (1 - C), C.
apply: boolp.funext => t'.
rewrite /false_assurance_hetero (bigD1 j) //= eqxx.
have Heq : \prod_(i < k | i != j) (1 - (if i == j then t' else c i)) = C.
  by apply: eq_bigr => i Hi; rewrite (negbTE Hi).
by rewrite Heq mulrBl mul1r opprB addrA addrAC.
Qed.

End ContinuityAndSmoothness.

Print Assumptions false_assurance_continuous_alpha.
Print Assumptions false_assurance_hetero_continuous_coord.
Print Assumptions false_assurance_hetero_derivable_coord.
Print Assumptions false_assurance_hetero_coord_affine.
