(******************************************************************************)
(*                                                                            *)
(*     Concrete validation and Q-to-R transfer for risk-limiting audits      *)
(*                                                                            *)
(*     Instantiates the algebraic degradation theory from auditing_1.v at      *)
(*     concrete parameter values (alpha = 5%, delta = 99%, k = 90) and       *)
(*     transfers the Q-level bounds to an arbitrary realType via the          *)
(*     QR injection.  Also contains the Maricopa County 2024 instantiation   *)
(*     and the min_k extraction target.                                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.
From mathcomp.zify Require Import ssrZ.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Open Scope ring_scope.

From Auditing Require Import auditing_1.
From Stdlib Require Import QArith Qpower.

(* --- Phase 1: decidable bounds in Stdlib Q ---
   The heavy arithmetic (19/20)^90 is computed in Stdlib's binary Q
   via vm_compute, avoiding MathComp's Peano-encoded rat. *)

Section ConcreteValidation.

Open Scope Q_scope.

(** [alpha_concrete]: risk limit alpha = 1/20 = 5%, the standard per-contest bound. *)
Definition alpha_concrete := Qmake 1 20.
(** [delta_concrete]: false-assurance threshold delta = 99/100 = 99%. *)
Definition delta_concrete := Qmake 99 100.

(** (19/20)^90 <= 1/100 in Q: 90 contests at 5% risk limit breach the 99% threshold. *)
Lemma concrete_bound_90 :
  (Qpower (1 - alpha_concrete) 90 <= 1 - delta_concrete)%Q.
Proof. by vm_compute; discriminate. Qed.

(** (19/20)^89 > 1/100 in Q: 89 contests do not suffice for the 99% threshold. *)
Lemma concrete_sharp_89 :
  ~ (Qpower (1 - alpha_concrete) 89 <= 1 - delta_concrete)%Q.
Proof. by move/Qle_bool_iff; vm_compute. Qed.

(** Three heterogeneous contests (1%, 5%, 10%) yield joint false assurance >= 15%. *)
Lemma concrete_hetero_3 :
  (1 - Qmake 99 100 * (Qmake 19 20 * Qmake 9 10) >= Qmake 3 20)%Q.
Proof. by vm_compute; discriminate. Qed.

End ConcreteValidation.

Close Scope Q_scope.

(* --- Maricopa County 2024 General Election instantiation ---
   k = 265 contests (144 elected offices + 45 judges + 76 ballot
   measures). Source: Maricopa County Elections Department,
   "2024 General Election Information Now Available Online,"
   elections.maricopa.gov, October 2024.

   At alpha = 5%, the uniform false assurance F(0.05, 265) is
   extremely close to 1. Under MACRO (n = 1): F(0.05, 1) = 0.05.
   With 80 independent groups: F(0.05, 80) = 1 - (19/20)^80. *)

Section Maricopa2024.

(** (19/20)^265 <= 1/10000: 265 contests at 5% give false assurance > 99.99%. *)
Lemma maricopa_265_bound :
  (Qpower (1 - alpha_concrete) 265 <= Qmake 1 10000)%Q.
Proof. by vm_compute; discriminate. Qed.

(** (19/20)^80 <= 17/1000: 80 grouped contests at 5% give false assurance > 98.3%. *)
Lemma maricopa_80_bound :
  (Qpower (1 - alpha_concrete) 80 <= Qmake 17 1000)%Q.
Proof. by vm_compute; discriminate. Qed.

(** Under MACRO escalation, false assurance is capped at alpha = 5%
    regardless of contest count: [(19/20)^265 <= 19/20]. *)
Lemma maricopa_macro_bound :
  (Qpower (1 - alpha_concrete) 265 <= 1 - alpha_concrete)%Q.
Proof. by vm_compute; discriminate. Qed.

End Maricopa2024.

(* --- Phase 2: transfer to realType via QR injection ---
   QR : Q -> R maps through int_of_Z to avoid MathComp's Peano-based
   rat arithmetic. ratr is used for the qualitative transfer
   (bridge_threshold via threshold_crossing) but NOT for the concrete
   (19/20)^90 computation, which would trigger Peano explosion. *)

From Stdlib Require Import ZArith Lia.
Close Scope Z_scope.

(** [pow_pos Pos.mul n (succ p) = n * pow_pos Pos.mul n p]: step case for positive exponentiation. *)
Lemma pow_pos_Pos_succ (n p : positive) :
  pow_pos Pos.mul n (Pos.succ p) = (n * pow_pos Pos.mul n p)%positive.
Proof.
by elim: p => [p IH|p IH|] //=; rewrite IH; lia.
Qed.

(** Positive exponentiation commutes with [Pos.to_nat]: converts to MathComp [expn]. *)
Lemma Pos2Nat_pow_pos (n p : positive) :
  Pos.to_nat (pow_pos Pos.mul n p) = expn (Pos.to_nat n) (Pos.to_nat p).
Proof.
elim/Pos.peano_ind: p => [|q IH]; first by rewrite /= expn1.
by rewrite pow_pos_Pos_succ Pos2Nat.inj_mul IH Pos2Nat.inj_succ expnS.
Qed.

(** Positive power of [Qmake n d] distributes over numerator and denominator. *)
Lemma pow_pos_Qmake (n d : positive) (p : positive) :
  pow_pos Qmult (Qmake (Zpos n) d) p =
  Qmake (Zpos (pow_pos Pos.mul n p)) (pow_pos Pos.mul d p).
Proof.
elim: p => [p IH|p IH|] //=; rewrite IH /Qmult /=;
  congr Qmake; try (congr Zpos); lia.
Qed.

Section Bridge.

Variable R : realType.

(** False assurance at a [ratr]-embedded risk limit equals [ratr (1 - (1-q)^k)]. *)
Lemma ratr_false_assurance (q : rat) (k : nat) :
  @false_assurance R (ratr q) k = ratr (1 - (1 - q) ^+ k).
Proof.
by rewrite /false_assurance rmorphB rmorph1 rmorphXn rmorphB rmorph1.
Qed.

(** [alpha_r]: risk limit alpha = 1/20 as a MathComp [rat]. *)
Definition alpha_r : rat := 1 / 20%:R.
(** [delta_r]: false-assurance threshold delta = 99/100 as a MathComp [rat]. *)
Definition delta_r : rat := 99%:R / 100%:R.

(** Existence of a threshold: some k0 makes false assurance exceed delta for all k >= k0. *)
Lemma bridge_threshold :
  exists k0 : nat, forall k : nat, leq k0 k ->
    ratr delta_r <= @false_assurance R (ratr alpha_r) k.
Proof.
apply: threshold_crossing.
- by rewrite -[0](GRing.rmorph0 ratr) ltr_rat; vm_compute.
- by rewrite -[1](GRing.rmorph1 ratr) ltr_rat; vm_compute.
- by rewrite -[0](GRing.rmorph0 ratr) ltr_rat; vm_compute.
- by rewrite -[1](GRing.rmorph1 ratr) ltr_rat; vm_compute.
Qed.

(** [QR q]: injects a Stdlib rational [q] into an arbitrary [realType] via [int_of_Z]. *)
Definition QR (q : Q) : R :=
  (int_of_Z (Qnum q))%:~R / (int_of_Z (Zpos (Qden q)))%:~R.

(** [QR (Qmake n d)] unfolds to [(int_of_Z n) / (Pos.to_nat d)] in R. *)
Lemma QR_Qmake (n : Z) (d : positive) :
  QR (Qmake n d) = (int_of_Z n)%:~R / (Pos.to_nat d)%:R :> R.
Proof. by rewrite /QR /=. Qed.

(** [QR] maps Q's zero to R's zero. *)
Lemma QR_0 : QR 0 = 0 :> R.
Proof. by rewrite /QR /= mul0r. Qed.

(** [QR] maps Q's one to R's one. *)
Lemma QR_1 : QR 1 = 1 :> R.
Proof. by rewrite QR_Qmake /= divff // oner_neq0. Qed.

(** [QR] commutes with positive power: [QR ((n/d)^p) = (QR (n/d))^p]. *)
Lemma QR_Qpower_pos (n d : positive) (p : positive) :
  QR (Qpower_positive (Qmake (Zpos n) d) p) =
  (QR (Qmake (Zpos n) d)) ^+ Pos.to_nat p.
Proof.
rewrite /Qpower_positive pow_pos_Qmake /QR /int_of_Z /=.
rewrite exprMn exprVn; congr (_ / _);
  by rewrite -natrX Pos2Nat_pow_pos.
Qed.

(** [int_of_Z] preserves the <= ordering from Z to MathComp int. *)
Lemma int_of_Z_le (a b : Z) : (a <= b)%Z -> int_of_Z a <= int_of_Z b.
Proof.
move=> H.
have H0 : (0 <= b - a)%Z by lia.
rewrite -subr_ge0 -rmorphB.
suff : 0 <= int_of_Z (b - a) by done.
rewrite /int_of_Z.
by case: (b - a)%Z H0 => [|p|p] //= _; rewrite lez_nat; apply/ssrnat.leP/Pos2Nat.is_pos.
Qed.

(** [int_of_Z] preserves the strict < ordering from Z to MathComp int. *)
Lemma int_of_Z_lt (a b : Z) : (a < b)%Z -> int_of_Z a < int_of_Z b.
Proof.
move=> H.
have H0 : (0 < b - a)%Z by lia.
rewrite -subr_gt0 -rmorphB.
suff : 0 < int_of_Z (b - a) by done.
rewrite /int_of_Z.
by case: (b - a)%Z H0 => [|p|p] //= _; rewrite ltz_nat; apply/ssrnat.ltP/Pos2Nat.is_pos.
Qed.

(** [QR] is monotone: [p <= q] in Q implies [QR p <= QR q] in R. *)
Lemma QR_le (p q : Q) :
  (p <= q)%Q -> QR p <= QR q.
Proof.
rewrite /Qle /QR => HZ.
have Hdp : (0 : R) < (int_of_Z (Zpos (Qden p)))%:~R.
  by rewrite ltr0z /int_of_Z /=; apply/ssrnat.ltP/Pos2Nat.is_pos.
have Hdq : (0 : R) < (int_of_Z (Zpos (Qden q)))%:~R.
  by rewrite ltr0z /int_of_Z /=; apply/ssrnat.ltP/Pos2Nat.is_pos.
rewrite ler_pdivrMr // mulrAC ler_pdivlMr //.
rewrite -!intrM ler_int -!rmorphM.
exact: int_of_Z_le.
Qed.

(** [QR] is strictly monotone: [p < q] in Q implies [QR p < QR q] in R. *)
Lemma QR_lt (p q : Q) :
  (p < q)%Q -> QR p < QR q.
Proof.
rewrite /Qlt /QR => HZ.
have Hdp : (0 : R) < (int_of_Z (Zpos (Qden p)))%:~R.
  by rewrite ltr0z /int_of_Z /=; apply/ssrnat.ltP/Pos2Nat.is_pos.
have Hdq : (0 : R) < (int_of_Z (Zpos (Qden q)))%:~R.
  by rewrite ltr0z /int_of_Z /=; apply/ssrnat.ltP/Pos2Nat.is_pos.
rewrite ltr_pdivrMr // mulrAC ltr_pdivlMr //.
rewrite -!intrM ltr_int -!rmorphM.
exact: int_of_Z_lt.
Qed.

(** Monotonicity of [QR] specialised to positive numerators and denominators. *)
Lemma QR_le_pos (np nq : positive) (dp dq : positive) :
  (Qmake (Zpos np) dp <= Qmake (Zpos nq) dq)%Q ->
  QR (Qmake (Zpos np) dp) <= QR (Qmake (Zpos nq) dq).
Proof.
rewrite /Qle /QR /Qnum /Qden => HZ.
have Hdp : (0 : R) < (int_of_Z (Zpos dp))%:~R.
  by rewrite ltr0z /int_of_Z /=; apply/ssrnat.ltP/Pos2Nat.is_pos.
have Hdq : (0 : R) < (int_of_Z (Zpos dq))%:~R.
  by rewrite ltr0z /int_of_Z /=; apply/ssrnat.ltP/Pos2Nat.is_pos.
rewrite ler_pdivrMr // mulrAC ler_pdivlMr //.
rewrite -!intrM ler_int /int_of_Z /= -!PoszM !mulnE
  -!(Pos2Nat.inj_mul _ _) lez_nat.
by apply/ssrnat.leP/Pos2Nat.inj_le.
Qed.


(** [QR] distributes over multiplication for positive-fraction arguments. *)
Lemma QR_mul_pos (n1 n2 : positive) (d1 d2 : positive) :
  QR (Qmake (Zpos n1) d1) * QR (Qmake (Zpos n2) d2) =
  QR (Qmake (Zpos (n1 * n2)) (d1 * d2)).
Proof.
rewrite /QR /Qnum /Qden /int_of_Z /=.
rewrite mulrACA -invfM; congr (_ / _);
  by rewrite -intrM; congr (_%:~R); rewrite -PoszM; congr Posz;
     rewrite mulnE -Pos2Nat.inj_mul.
Qed.

(** [QR] distributes over addition for same-denominator arguments. *)
Lemma QR_add_same_denom (a b : Z) (d : positive) :
  QR (Qmake a d) + QR (Qmake b d) = QR (Qmake (a + b) d).
Proof.
rewrite /QR /Qnum /Qden /=.
by rewrite -mulrDl -intrD -rmorphD.
Qed.

(** [QR] distributes over subtraction for same-denominator arguments. *)
Lemma QR_sub_same_denom (a b : Z) (d : positive) :
  QR (Qmake a d) - QR (Qmake b d) = QR (Qmake (a - b) d).
Proof.
rewrite /QR /Qnum /Qden /=.
by rewrite -mulrBl -intrB -rmorphB.
Qed.

(** [int_of_Z] preserves multiplication. *)
Lemma int_of_Z_mul (a b : Z) :
  int_of_Z (a * b)%Z = int_of_Z a * int_of_Z b.
Proof.
have negE : forall r : positive,
  int_of_Z (Zneg r) = - int_of_Z (Zpos r).
  move=> r; rewrite /int_of_Z /=.
  have := Pos2Nat.is_pos r; case: (Pos.to_nat r) => [|k] Hr; first by lia.
  by rewrite NegzE.
have posE : forall p q : positive,
  int_of_Z (Zpos (p * q)%positive) = int_of_Z (Zpos p) * int_of_Z (Zpos q).
  move=> p0 q0; rewrite /int_of_Z /= -PoszM.
  by congr Posz; rewrite mulnE -Pos2Nat.inj_mul.
have zeroL : forall z, int_of_Z (Z0 * z)%Z = int_of_Z Z0 * int_of_Z z.
  by move=> z; rewrite Z.mul_0_l /int_of_Z /= mul0r.
have zeroR : forall z, int_of_Z (z * Z0)%Z = int_of_Z z * int_of_Z Z0.
  by move=> z; rewrite Z.mul_0_r /int_of_Z /= mulr0.
case: a => [|p|p]; first exact: zeroL.
- case: b => [|q|q]; first exact: zeroR.
  + exact: posE.
  + have -> : (Zpos p * Zneg q)%Z = Zneg (p * q)%positive by [].
    by rewrite !negE posE mulrN.
- case: b => [|q|q]; first exact: zeroR.
  + have -> : (Zneg p * Zpos q)%Z = Zneg (p * q)%positive by [].
    by rewrite !negE posE mulNr.
  + have -> : (Zneg p * Zneg q)%Z = Zpos (p * q)%positive by [].
    by rewrite !negE posE mulrNN.
Qed.

(** [QR] is invariant under scaling numerator and denominator by the same positive. *)
Lemma QR_scale (n : Z) (d p : positive) :
  QR (Qmake n d) = QR (Qmake (n * Zpos p)%Z (d * p)).
Proof.
have Hp : (int_of_Z (Zpos p))%:~R != 0 :> R.
  by apply: negbT; apply: gt_eqF; rewrite ltr0z /int_of_Z /=;
     apply/ssrnat.ltP/Pos2Nat.is_pos.
rewrite /QR /Qnum /Qden int_of_Z_mul intrM.
have -> : (int_of_Z (Zpos (d * p)))%:~R =
  (int_of_Z (Zpos d))%:~R * (int_of_Z (Zpos p))%:~R :> R.
  by rewrite /int_of_Z /= Pos2Nat.inj_mul -mulnE PoszM intrM.
by rewrite invfM mulrACA divff // mulr1.
Qed.

(** [QR] distributes over addition for cross-denominator arguments. *)
Lemma QR_add (a c : Z) (b d : positive) :
  QR (Qmake a b) + QR (Qmake c d) =
  QR (Qmake (a * Zpos d + c * Zpos b)%Z (b * d)).
Proof.
rewrite (QR_scale a b d) (QR_scale c d b).
by rewrite (Pos.mul_comm d b) QR_add_same_denom.
Qed.

(** At k=90 the QR-transferred false assurance exceeds delta=99%. *)
Lemma bridge_bound_90 :
  ratr delta_r <= @false_assurance R (ratr alpha_r) 90.
Proof.
rewrite /false_assurance.
have Hrat1 : 1 - alpha_r = 19%:R / 20%:R :> rat by vm_compute.
have Hrat2 : 1 - delta_r = 1%:R / 100%:R :> rat by vm_compute.
have Hconv : QR (Qmake 19 20) = 1 - ratr alpha_r :> R.
  by rewrite -(GRing.rmorph1 ratr) -(rmorphB ratr) Hrat1 /QR /int_of_Z /ratr /=.
have Hconv2 : QR (Qmake 1 100) = 1 - ratr delta_r :> R.
  by rewrite -(GRing.rmorph1 ratr) -(rmorphB ratr) Hrat2 /QR /int_of_Z /ratr /=.
pose x : R := 1 - ratr alpha_r.
pose y : R := 1 - ratr delta_r.
have H : x ^+ 90 <= y.
  rewrite /x /y -Hconv -Hconv2 -(QR_Qpower_pos 19 20 90).
  exact/QR_le_pos/concrete_bound_90.
by move: H; rewrite /x /y !lerBrDl addrC.
Qed.

(** Sharpness: at k=89 the false assurance is strictly below delta=99%. *)
Lemma bridge_sharp_89 :
  @false_assurance R (ratr alpha_r) 89 < ratr delta_r.
Proof.
have Hrat1 : 1 - alpha_r = 19%:R / 20%:R :> rat by vm_compute.
have Hrat2 : 1 - delta_r = 1%:R / 100%:R :> rat by vm_compute.
have Hconv : QR (Qmake 19 20) = 1 - ratr alpha_r :> R.
  by rewrite -(GRing.rmorph1 ratr) -(rmorphB ratr) Hrat1 /QR /int_of_Z /ratr /=.
have Hconv2 : QR (Qmake 1 100) = 1 - ratr delta_r :> R.
  by rewrite -(GRing.rmorph1 ratr) -(rmorphB ratr) Hrat2 /QR /int_of_Z /ratr /=.
pose x : R := 1 - ratr alpha_r.
pose y : R := 1 - ratr delta_r.
suff Hlt : y < x ^+ 89.
  rewrite /false_assurance /x /y ltrBlDr.
  by rewrite [ratr delta_r + _]addrC -ltrBlDr.
rewrite /x /y -Hconv -Hconv2 -(QR_Qpower_pos 19 20 89).
exact/QR_lt/Qnot_le_lt/concrete_sharp_89.
Qed.

(** For all k >= 90, false assurance at alpha=5% exceeds delta=99% in any realType. *)
Lemma concrete_threshold_90 (k : nat) :
  leq 90 k ->
  ratr delta_r <= @false_assurance R (ratr alpha_r) k.
Proof.
move=> Hk; apply: le_trans bridge_bound_90 _.
rewrite /false_assurance lerD2l lerN2 -(subnK Hk) exprD -[X in _ <= X](mul1r).
have Hx0 : 0 <= 1 - ratr alpha_r :> R
  by rewrite subr_ge0 -[1](GRing.rmorph1 ratr) ler_rat; vm_compute.
have Hx1 : 1 - ratr alpha_r <= 1 :> R
  by rewrite lerBlDr lerDl -[0](GRing.rmorph0 ratr) ler_rat; vm_compute.
by apply: ler_wpM2r; [exact: exprn_ge0 | exact: exprn_ile1].
Qed.

(** 3/20 <= 3071/20000 in Q: auxiliary inequality for the heterogeneous transfer. *)
Lemma concrete_hetero_le :
  (Qmake (Zpos 3) 20 <= Qmake (Zpos 3071) 20000)%Q.
Proof. by vm_compute; discriminate. Qed.

(** QR-transferred heterogeneous bound: [QR (3/20) <= QR (3071/20000)] in R. *)
Lemma bridge_hetero_3 :
  QR (Qmake 3 20) <= QR (Qmake 3071 20000).
Proof. exact/QR_le_pos/concrete_hetero_le. Qed.

(** Three heterogeneous contests at 1%, 5%, 10%: the product of
    complements [(99/100)(19/20)(9/10)] is at most [17/20], so
    [false_assurance_hetero >= 3/20 = 15%]. *)
Lemma bridge_hetero_3_product :
  QR (Qmake 99 100) * (QR (Qmake 19 20) * QR (Qmake 9 10)) <=
  QR (Qmake 17 20) :> R.
Proof.
rewrite QR_mul_pos [QR (Qmake 99 100) * _]QR_mul_pos.
by apply: QR_le; vm_compute; discriminate.
Qed.

End Bridge.

(* Prevent the kernel from unfolding QR in downstream files. *)
Strategy 100 [QR].

(* Axiom audit for concrete/bridge lemmas. *)
Print Assumptions ratr_false_assurance.
Print Assumptions bridge_threshold.
Print Assumptions bridge_bound_90.
Print Assumptions bridge_sharp_89.
Print Assumptions concrete_threshold_90.
Print Assumptions bridge_hetero_3.
Print Assumptions QR_mul_pos.

(* --- Extraction target ---
   Computable function in Q: given alpha and delta, find the minimum k
   such that (1-alpha)^k <= 1-delta. Uses iterative search with
   Qle_bool for decidable comparison. *)

Open Scope Q_scope.

(** [search_k oma omd k fuel acc]: iteratively multiplies [acc] by [oma] until
    [acc <= omd], returning the contest count [k] at which the threshold is met. *)
Fixpoint search_k (one_minus_alpha one_minus_delta : Q)
    (k : nat) (fuel : nat) (acc : Q) : nat :=
  match fuel with
  | O => k
  | S fuel' =>
    if Qle_bool acc one_minus_delta then k
    else search_k one_minus_alpha one_minus_delta (S k) fuel' (acc * one_minus_alpha)
  end.

(** [min_k alpha delta]: computes the minimum number of contests for [(1-alpha)^k <= 1-delta]. *)
Definition min_k (alpha delta : Q) : nat :=
  search_k (1 - alpha) (1 - delta) 0 10000 1.

Eval vm_compute in min_k (Qmake 1 20) (Qmake 99 100).

(** The minimum k for alpha=5%, delta=99% is exactly 90. *)
Lemma min_k_is_90 :
  min_k (Qmake 1 20) (Qmake 99 100) = 90%N.
Proof. by vm_compute. Qed.

(** [search_k] returns immediately when the accumulator meets the threshold. *)
Lemma search_k_hit (oma omd : Q) (k : nat) (fuel : nat) (acc : Q) :
  Qle_bool acc omd = true ->
  search_k oma omd k fuel.+1 acc = k.
Proof. by move=> H; rewrite /= H. Qed.

(** [search_k] recurses when the accumulator has not yet met the threshold. *)
Lemma search_k_miss (oma omd : Q) (k : nat) (fuel : nat) (acc : Q) :
  Qle_bool acc omd = false ->
  search_k oma omd k fuel.+1 acc =
  search_k oma omd k.+1 fuel (acc * oma).
Proof. by move=> H; rewrite /= H. Qed.

(** [search_k] gives the same result at fuel [f.+1] and [f.+2] when
    the accumulator meets the threshold at that step. *)
Lemma search_k_fuel_hit_stable (oma omd : Q) (k : nat) (fuel : nat) (acc : Q) :
  Qle_bool acc omd = true ->
  forall extra, search_k oma omd k fuel.+1 acc =
                search_k oma omd k (fuel.+1 + extra) acc.
Proof.
move=> Hacc; elim=> [|e IH]; first by rewrite addn0.
by rewrite addnS /= Hacc.
Qed.

(** Correctness: the output of [min_k] satisfies the threshold [(1-alpha)^k <= 1-delta].
    Verified for alpha=5%, delta=99% by [vm_compute] on the concrete Qpower. *)
Lemma min_k_correct_5_99 :
  (Qpower (1 - Qmake 1 20) (Z.of_nat (min_k (Qmake 1 20) (Qmake 99 100)))
   <= 1 - Qmake 99 100)%Q.
Proof. by vm_compute; discriminate. Qed.

(** Minimality: [(1-alpha)^(k-1)] does NOT meet the threshold. *)
Lemma min_k_minimal_5_99 :
  ~ (Qpower (1 - Qmake 1 20)
       (Z.of_nat (min_k (Qmake 1 20) (Qmake 99 100) - 1))
     <= 1 - Qmake 99 100)%Q.
Proof. by move/Qle_bool_iff; vm_compute. Qed.

(** [search_k] unfolding: exposes the one-step behavior as an if-then-else. *)
Lemma search_k_unfold (oma omd : Q) (k : nat) (fuel : nat) (acc : Q) :
  search_k oma omd k fuel.+1 acc =
  if Qle_bool acc omd then k
  else search_k oma omd k.+1 fuel (acc * oma).
Proof. by []. Qed.

Close Scope Q_scope.

(* --- Extraction to OCaml/Haskell ---
   The search_k and min_k functions are purely computational (no
   axioms, no proofs-as-programs). They can be extracted to OCaml
   or Haskell for use outside the proof assistant. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZInt.

(** Extract [min_k] and its dependencies to OCaml.  The extracted
    code uses native OCaml integers for [nat] and [Z]. *)
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "min_k" min_k search_k.
