Set Implicit Arguments.
Unset Strict Implicit.
Require Import List.
Import ListNotations.
Require Import Arith.EqNat.
Require Import Arith.Le.

Inductive form : Type :=
| free_var (x : nat)
| bound_var (x : nat) 
| bot 
| imp (s t : form)
| conj (s t : form)
| disj (s t : form)
| for_all (s : form)
| exist (s : form).

Inductive not_free_in : nat -> form -> Prop :=
  |NF_free_var (m n : nat) : m <> n -> not_free_in m (free_var n)
  |NF_bound_var (m n : nat) : not_free_in m (bound_var n)
  |NF_bot (n : nat) : not_free_in n bot
  |NF_imp (n : nat) (s t : form) : not_free_in n s -> not_free_in n t -> not_free_in n (imp s t)
  |NF_conj (n : nat) (s t : form) : not_free_in n s -> not_free_in n t -> not_free_in n (conj s t)
  |NF_disj (n : nat) (s t : form) : not_free_in n s -> not_free_in n t -> not_free_in n (disj s t)
  |NF_for_all (n : nat) (s : form) : not_free_in n s -> not_free_in n (for_all s)
  |NF_exist (n : nat) (s : form) : not_free_in n s -> not_free_in n (exist s).

Inductive not_free_in_ctx : nat -> list form -> Prop :=
  |NFC_nil (x : nat) : not_free_in_ctx x []
  |NFC_l (x : nat) (s : form) (A : list form) : not_free_in x s -> not_free_in_ctx x A -> not_free_in_ctx x (s::A).

(*
Fixpoint bind_height (x height : nat) (s : form) : form :=
  match s with
  | free_var n => if Nat.eqb x n then bound_var height else free_var n
  | bound_var n => bound_var n
  | bot => bot
  | imp s t => imp (bind_height x height s) (bind_height x height t)
  | conj s t => conj (bind_height x height s) (bind_height x height t)
  | disj s t => disj (bind_height x height s) (bind_height x height t)
  | for_all s => for_all (bind_height x (S height) s)
  | exist s => exist (bind_height x (S height) s)
  end.

Definition bind (x : nat) (s : form) : form :=
  bind_height x 0 s.

Definition my_for_all (x : nat) (s : form) : form :=
  for_all (bind x s).

Definition my_exist (x : nat) (s : form) : form :=
  exist (bind x s).
*)

Definition unbind (s : form) (x : nat) : form :=
  let fix aux (s : form) (x height : nat) : form :=
  match s with
    | free_var n => free_var n
    | bound_var n => if Nat.eqb height n then free_var x else bound_var n
    | bot => bot
    | imp s t => imp (aux s x height) (aux t x height)
    | conj s t => conj (aux s x height) (aux t x height)
    | disj s t => disj (aux s x height) (aux t x height)
    | for_all s => for_all (aux s x (S height))
    | exist s => exist (aux s x (S height))
    end
  in aux s x 0.

Print In.
Print incl.

Notation "s ~> t" := (imp s t) ( at level 51, right associativity).
Notation neg s := ( imp s bot).
Reserved Notation "A |- s" (at level 70).

(** 2.a *)
Inductive nd : list form -> form -> Prop :=
  |Ass A s : (In s A) -> nd A s
  |Exp A s : nd A bot -> nd A s
  |Iimp A s t : nd (s::A) t -> nd A (s ~> t)
  |Eimp A s t : nd A s -> nd A (s ~> t) -> nd A t
  |Iconj A s t : nd A s -> nd A t -> nd A (conj s t)
  |Econjr A s t : nd A (conj s t) -> nd A t
  |Econjl A s t : nd A (conj s t) -> nd A s
  |Idisjr A s t : nd A t -> nd A (disj s t)
  |Idisjl A s t : nd A s -> nd A (disj s t)
  |Edisj A s t u : nd A (disj s t) -> nd A (imp s u) -> nd A (imp t u) -> nd A u
  |Ifor_all A s x : not_free_in_ctx x A -> not_free_in x s -> nd A (unbind s x) -> nd A (for_all s)
  |Efor_all A s x : nd A (for_all s) -> nd A (unbind s x)
  |Iexist A s x : nd A (unbind s x) -> nd A (exist s)
  |Eexist A s t x : not_free_in_ctx x A -> not_free_in x s -> not_free_in x t -> nd A (exist s) -> nd A (imp (unbind s x) t) -> nd A t.


Notation "A |- s" := (nd A s) ( at level 70).

(* Properties of not_free_in *)

Lemma NF_free_var_eq (x n : nat) :
  not_free_in x (free_var n) <-> x <> n.
Proof.
  split.
  - intro NF.
    remember (free_var n) as s.
    induction NF.
    + injection Heqs.
      intro H0.
      rewrite <- H0.
      assumption.
    + discriminate Heqs.
    + discriminate Heqs.
    + discriminate Heqs.
    + discriminate Heqs.
    + discriminate Heqs.
    + discriminate Heqs.
    + discriminate Heqs.
  - intro H.
    apply NF_free_var.
    assumption.
Qed.

Lemma NF_imp_eq (x : nat) (s t : form) :
  not_free_in x (imp s t) <-> not_free_in x s /\ not_free_in x t.
Proof.
  split.
  - intro NF.
    remember (imp s t) as u.
    induction NF.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + injection Hequ.
      intros H2 H1.
      rewrite H1 in NF1.
      rewrite H2 in NF2.
      split.
      * assumption.
      * assumption.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
  - intro H.
    destruct H.
    apply NF_imp.
    + assumption.
    + assumption.
Qed.

Lemma NF_conj_eq (x : nat) (s t : form) :
  not_free_in x (conj s t) <-> not_free_in x s /\ not_free_in x t.
Proof.
  split.
  - intro NF.
    remember (conj s t) as u.
    induction NF.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + injection Hequ.
      intros H2 H1.
      rewrite H1 in NF1.
      rewrite H2 in NF2.
      split.
      * assumption.
      * assumption.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
  - intro H.
    destruct H.
    apply NF_conj.
    + assumption.
    + assumption.
Qed.

Lemma NF_disj_eq (x : nat) (s t : form) :
  not_free_in x (disj s t) <-> not_free_in x s /\ not_free_in x t.
Proof.
  split.
  - intro NF.
    remember (disj s t) as u.
    induction NF.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + injection Hequ.
      intros H2 H1.
      rewrite H1 in NF1.
      rewrite H2 in NF2.
      split.
      * assumption.
      * assumption.
    + discriminate Hequ.
    + discriminate Hequ.
  - intro H.
    destruct H.
    apply NF_disj.
    + assumption.
    + assumption.
Qed.

Lemma NF_for_all_eq (x : nat) (s : form) :
  not_free_in x (for_all s) <-> not_free_in x s.
Proof.
  split.
  - intro NF.
    remember (for_all s) as u.
    induction NF.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + injection Hequ.
      intro H.
      rewrite H in NF.
      assumption.
    + discriminate Hequ.
  - intro H.
    apply NF_for_all.
    assumption.
Qed.

Lemma NF_exist_eq (x : nat) (s : form) :
  not_free_in x (exist s) <-> not_free_in x s.
Proof.
  split.
  - intro NF.
    remember (exist s) as u.
    induction NF.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + discriminate Hequ.
    + injection Hequ.
      intro H.
      rewrite H in NF.
      assumption.
  - intro H.
    apply NF_exist.
    assumption.
Qed.

(* Properties of not_free_in_ctx *)

Lemma NFC_in (A : list form) (x : nat) (a : form) : In a A -> not_free_in_ctx x A -> not_free_in x a.
Proof.
  intros I NFCA.
  induction NFCA.
  - apply in_nil in I. contradiction.
  - apply in_inv in I. destruct I.
    + rewrite <- H0. assumption.
    + apply IHNFCA. assumption.
Qed.

Lemma NFC_incl (A B : list form) (x : nat) : incl A B -> not_free_in_ctx x B -> not_free_in_ctx x A.
Proof.
  induction A.
  - intros I NFCA.
    constructor.
  - intros I NFCA.
    constructor.
    + apply NFC_in with (A := B).
      * unfold incl in I.
        apply I.
        apply in_eq.
      * assumption.
    + apply IHA.
      * apply incl_tran with (m := a::A).
        apply incl_tl.
        apply incl_refl.
        assumption.
      * assumption.
Qed.

Lemma NFC_l_eq (s : form) (A : list form) (x : nat) :
  not_free_in_ctx x (s::A) <-> not_free_in x s /\ not_free_in_ctx x A.
Proof.
  split.
  - intro NFC.
    remember (s::A) as B.
    induction NFC.
    + discriminate HeqB.
    + injection HeqB.
      intros HA Hs.
      split.
      * rewrite <- Hs.
        assumption.
      * rewrite <- HA.
        assumption.
  - intro NFC.
    destruct NFC as (NFCs,NFCA).
    apply NFC_l.
    + assumption.
    + assumption.
Qed.

(* Proving that, given a context, there exists a variable which does not appear as a free variable in this context *)

Lemma NF_bounded (s : form) :
  exists (x0 : nat), forall (x : nat), x >= x0 -> not_free_in x s.
Proof.
  induction s.
  - exists (S x).
    intros x0 Ineq.
    apply NF_free_var.
    Search Nat.lt.
    intro H.
    rewrite H in Ineq.
    apply Nat.nle_succ_diag_l with (n := x).
    assumption.
  - exists 0.
    intros x0 Ineq.
    apply NF_bound_var.
  - exists 0.
    intros x0 Ineq.
    apply NF_bot.
  - destruct IHs1.
    destruct IHs2.
    exists (Nat.max x x0).
    intros y H1.
    apply NF_imp.
    + apply H.
      apply Nat.le_trans with (m := Nat.max x x0).
      * apply Nat.le_max_l.
      * assumption.
    + apply H0.
      apply Nat.le_trans with (m := Nat.max x x0).
      * apply Nat.le_max_r.
      * assumption.
  - destruct IHs1.
    destruct IHs2.
    exists (Nat.max x x0).
    intros y H1.
    apply NF_conj.
    + apply H.
      apply Nat.le_trans with (m := Nat.max x x0).
      * apply Nat.le_max_l.
      * assumption.
    + apply H0.
      apply Nat.le_trans with (m := Nat.max x x0).
      * apply Nat.le_max_r.
      * assumption.
  - destruct IHs1.
    destruct IHs2.
    exists (Nat.max x x0).
    intros y H1.
    apply NF_disj.
    + apply H.
      apply Nat.le_trans with (m := Nat.max x x0).
      * apply Nat.le_max_l.
      * assumption.
    + apply H0.
      apply Nat.le_trans with (m := Nat.max x x0).
      * apply Nat.le_max_r.
      * assumption.
  - destruct IHs.
    exists x.
    intros y H1.
    apply NF_for_all.
    apply H.
    assumption.
  - destruct IHs.
    exists x.
    intros y H1.
    apply NF_exist.
    apply H.
    assumption.
Qed.

Lemma NFC_bounded (A : list form) :
  exists (x0 : nat), forall (x : nat), x >= x0 -> not_free_in_ctx x A.
Proof.
  induction A.
  - exists 0.
    intros x H.
    apply NFC_nil.
  - destruct (NF_bounded a).
    destruct IHA.
    exists (Nat.max x x0).
    intros y H1.
    apply NFC_l.
    + apply H.
      apply Nat.le_trans with (m := Nat.max x x0).
      * apply Nat.le_max_l.
      * assumption.
    + apply H0.
      apply Nat.le_trans with (m := Nat.max x x0).
      * apply Nat.le_max_r.
      * assumption.
Qed.

Lemma NFC_existence (A : list form) :
  exists (x : nat), not_free_in_ctx x A.
Proof.
  destruct (NFC_bounded A).
  exists x.
  apply H.
  apply Nat.le_refl.
Qed.

(* Defining a function nat -> nat which swaps two integers *)

Definition exchange_nat (x y z : nat) : nat :=
  if Nat.eqb z x then y else if Nat.eqb z y then x else z.

(*
Lemma exchange_nat_refl (x y : nat) :
  exchange_nat x x y = y.
Proof.
  unfold exchange_nat.
  destruct (Bool.bool_dec (Nat.eqb y x) true) as [Eq | Neq].
  + rewrite Eq.
    apply Nat.eqb_eq.
    rewrite Nat.eqb_sym with (x := x) (y := y).
    assumption.
  + apply Bool.not_true_iff_false in Neq.
    rewrite Neq.
    reflexivity.
Qed.
*)

(*
Lemma exchange_nat_sym (x y z : nat) :
  exchange_nat x y z = exchange_nat y x z.
Proof.
  unfold exchange_nat.
  destruct (Bool.bool_dec (Nat.eqb z x) true) as [Eq | Neq].
  + rewrite Eq.
    destruct (Bool.bool_dec (Nat.eqb z y) true) as [Eq1 | Neq1].
    * rewrite Eq1.
      apply eq_trans with (y := z).
      apply eq_sym.
      apply Nat.eqb_eq.
      assumption.
      apply Nat.eqb_eq.
      assumption.
    * apply Bool.not_true_iff_false in Neq1.
      rewrite Neq1.
      reflexivity.
  + apply Bool.not_true_iff_false in Neq.
    rewrite Neq.
    destruct (Bool.bool_dec (Nat.eqb z y) true) as [Eq1 | Neq1].
    * rewrite Eq1.
      reflexivity.
    * apply Bool.not_true_iff_false in Neq1.
      rewrite Neq1.
      reflexivity.
Qed.
*)

Lemma exchange_nat_l (x y : nat) :
  exchange_nat x y x = y.
Proof.
  unfold exchange_nat.
  rewrite (Nat.eqb_refl x).
  reflexivity.
Qed.

Lemma exchange_nat_r (x y : nat) :
  exchange_nat x y y = x.
Proof.
  unfold exchange_nat.
  destruct (Bool.bool_dec (Nat.eqb y x) true) as [Eq | Neq].
  - rewrite Eq.
    apply Nat.eqb_eq.
    assumption.
  - apply Bool.not_true_iff_false in Neq.
    rewrite Neq.
    rewrite (Nat.eqb_refl y).
    reflexivity.
Qed.

Lemma exchange_nat_inv (x y z : nat) :
  exchange_nat x y (exchange_nat x y z) = z.
Proof.
  unfold exchange_nat.
  destruct (Bool.bool_dec (Nat.eqb z x) true) as [Eq | Neq].
  + rewrite Eq.
    destruct (Bool.bool_dec (Nat.eqb y x) true) as [Eq1 | Neq1].
    * rewrite Eq1.
      apply eq_trans with (y := x).
      apply Nat.eqb_eq.
      assumption.
      apply eq_sym.
      apply Nat.eqb_eq.
      assumption.
    * apply Bool.not_true_iff_false in Neq1.
      rewrite Neq1.
      rewrite (Nat.eqb_refl y).
      apply eq_sym.
      apply Nat.eqb_eq.
      assumption.
  + apply Bool.not_true_iff_false in Neq.
    rewrite Neq.
    destruct (Bool.bool_dec (Nat.eqb z y) true) as [Eq1 | Neq1].
    * rewrite Eq1.
      rewrite (Nat.eqb_refl x).
      apply eq_sym.
      apply Nat.eqb_eq.
      assumption.
    * apply Bool.not_true_iff_false in Neq1.
      rewrite Neq1.
      rewrite Neq.
      rewrite Neq1.
      reflexivity.
Qed.

(* Exchanging all the occurences of two variables in a formula *)

Fixpoint exchange_vars (s : form) (x y : nat) : form :=
  match s with
  | free_var n => free_var (exchange_nat x y n)
  | bound_var n => bound_var n
  | bot => bot
  | imp s t => imp (exchange_vars s x y) (exchange_vars t x y)
  | conj s t => conj (exchange_vars s x y) (exchange_vars t x y)
  | disj s t => disj (exchange_vars s x y) (exchange_vars t x y)
  | for_all s => for_all (exchange_vars s x y)
  | exist s => exist (exchange_vars s x y)
  end.

(*
Lemma exchange_vars_refl (s : form) (x : nat) :
  exchange_vars s x x = s.
Proof.
  induction s.
  - unfold exchange_vars.
    apply f_equal.
    apply exchange_nat_refl.
  - reflexivity.
  - reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs.
    reflexivity.
Qed.
*)

(*
Lemma exchange_vars_sym (s : form) (x y : nat) :
  exchange_vars s x y = exchange_vars s y x.
Proof.
  induction s.
  - simpl exchange_vars.
    apply f_equal.
    apply exchange_nat_sym.
  - reflexivity.
  - reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs.
    reflexivity.
Qed.
*)

Lemma exchange_vars_inv (s : form) (x y : nat) :
  exchange_vars (exchange_vars s x y) x y = s.
Proof.
  induction s.
  - simpl exchange_vars.
    apply f_equal.
    apply exchange_nat_inv.
  - reflexivity.
  - reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs.
    reflexivity.
  - simpl exchange_vars.
    rewrite IHs.
    reflexivity.
Qed.

Lemma exchange_vars_NF (s : form) (x y z : nat) :
  not_free_in z (exchange_vars s x y) <-> not_free_in (exchange_nat x y z) s.
Proof.
  induction s.
  - simpl exchange_vars.
    rewrite NF_free_var_eq.
    rewrite NF_free_var_eq.
    split; intros H1 H2; apply H1.
    + rewrite <- H2.
      apply eq_sym.
      apply exchange_nat_inv.
    + rewrite H2.
      apply exchange_nat_inv.
  - split; intro H; apply NF_bound_var.
  - split; intro H; apply NF_bot.
  - split; intro H.
    + apply NF_imp.
      * apply IHs1.
        apply NF_imp_eq with (t := exchange_vars s2 x y).
        assumption.
      * apply IHs2.
        apply NF_imp_eq with (s := exchange_vars s1 x y).
        assumption.
    + apply NF_imp.
      * apply IHs1.
        apply NF_imp_eq with (t := s2).
        assumption.
      * apply IHs2.
        apply NF_imp_eq with (s := s1).
        assumption.
  - split; intro H.
    + apply NF_conj.
      * apply IHs1.
        apply NF_conj_eq with (t := exchange_vars s2 x y).
        assumption.
      * apply IHs2.
        apply NF_conj_eq with (s := exchange_vars s1 x y).
        assumption.
    + apply NF_conj.
      * apply IHs1.
        apply NF_conj_eq with (t := s2).
        assumption.
      * apply IHs2.
        apply NF_conj_eq with (s := s1).
        assumption.
  - split; intro H.
    + apply NF_disj.
      * apply IHs1.
        apply NF_disj_eq with (t := exchange_vars s2 x y).
        assumption.
      * apply IHs2.
        apply NF_disj_eq with (s := exchange_vars s1 x y).
        assumption.
    + apply NF_disj.
      * apply IHs1.
        apply NF_disj_eq with (t := s2).
        assumption.
      * apply IHs2.
        apply NF_disj_eq with (s := s1).
        assumption.
  - split; intro H; apply NF_for_all; apply IHs; apply NF_for_all_eq; assumption.
  - split; intro H; apply NF_exist; apply IHs; apply NF_exist_eq; assumption.
Qed.

Lemma exchange_vars_unbind (s : form) (x y z : nat) :
  exchange_vars (unbind s z) x y = unbind (exchange_vars s x y) (exchange_nat x y z).
Proof.
  unfold unbind.
  generalize 0.
  induction s; intro height.
  - reflexivity.
  - simpl exchange_vars.
    destruct (Bool.bool_dec (Nat.eqb height x0) true) as [Eq | Neq].
    + rewrite Eq.
      reflexivity.
    + apply Bool.not_true_iff_false in Neq.
      rewrite Neq.
      reflexivity.
  - reflexivity.
  - simpl exchange_vars.
    unfold unbind.
    apply f_equal2.
    + apply IHs1.
    + apply IHs2.
  - simpl exchange_vars.
    unfold unbind.
    apply f_equal2.
    + apply IHs1.
    + apply IHs2.
  - simpl exchange_vars.
    unfold unbind.
    apply f_equal2.
    + apply IHs1.
    + apply IHs2.
  - simpl exchange_vars.
    unfold unbind.
    apply f_equal.
    apply IHs.
  - simpl exchange_vars.
    unfold unbind.
    apply f_equal.
    apply IHs.
Qed.

Lemma exchange_non_free_vars (s : form) (x y : nat) :
  not_free_in x s -> not_free_in y s -> exchange_vars s x y = s.
Proof.
  induction s; intros NFx NFy.
  - apply NF_free_var_eq in NFx.
    apply Nat.eqb_neq in NFx.
    rewrite Nat.eqb_sym in NFx.
    apply NF_free_var_eq in NFy.
    apply Nat.eqb_neq in NFy.
    rewrite Nat.eqb_sym in NFy.
    simpl exchange_vars.
    unfold exchange_nat.
    rewrite NFx.
    rewrite NFy.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl exchange_vars.
    apply f_equal2.
    + apply IHs1; apply NF_imp_eq with (t := s2); assumption.
    + apply IHs2; apply NF_imp_eq with (s := s1); assumption.
  - simpl exchange_vars.
    apply f_equal2.
    + apply IHs1; apply NF_conj_eq with (t := s2); assumption.
    + apply IHs2; apply NF_conj_eq with (s := s1); assumption.
  - simpl exchange_vars.
    apply f_equal2.
    + apply IHs1; apply NF_disj_eq with (t := s2); assumption.
    + apply IHs2; apply NF_disj_eq with (s := s1); assumption.
  - simpl exchange_vars.
    apply f_equal.
    apply IHs; apply NF_for_all_eq; assumption.
  - simpl exchange_vars.
    apply f_equal.
    apply IHs; apply NF_exist_eq; assumption.
Qed.

(* Exchanging the occurences of two variables in a context *)

Definition exchange_vars_ctx (A : list form) (x y : nat) : list form :=
  map (fun (s : form) => exchange_vars s x y) A.

(*
Lemma exchange_vars_ctx_refl (A : list form) (x : nat) :
  exchange_vars_ctx A x x = A.
Proof.
  induction A.
  - reflexivity.
  - simpl exchange_vars_ctx.
    apply f_equal2.
    + apply exchange_vars_refl.
    + assumption.
Qed.
*)

(*
Lemma exchange_vars_ctx_sym (A : list form) (x y : nat) :
  exchange_vars_ctx A x y = exchange_vars_ctx A y x.
Proof.
  induction A.
  - reflexivity.
  - simpl exchange_vars_ctx.
    apply f_equal2.
    + apply exchange_vars_sym.
    + assumption.
Qed.
*)

Lemma exchange_vars_ctx_inv (A : list form) (x y : nat) :
  exchange_vars_ctx (exchange_vars_ctx A x y) x y = A.
Proof.
  induction A.
  - reflexivity.
  - simpl exchange_vars_ctx.
    apply f_equal2.
    + apply exchange_vars_inv.
    + assumption.
Qed.

Lemma exchange_vars_ctx_NF_aux (A : list form) (x y z : nat) :
  not_free_in_ctx (exchange_nat x y z) A -> not_free_in_ctx z (exchange_vars_ctx A x y).
Proof.
  intro NFC.
  remember (exchange_nat x y z) as x0.
  induction NFC.
  - apply NFC_nil.
  - apply NFC_l.
    + apply exchange_vars_NF.
      rewrite <- Heqx0.
      assumption.
    + apply IHNFC.
      assumption.
Qed.

Lemma exchange_vars_ctx_NF (A : list form) (x y z : nat) :
  not_free_in_ctx z (exchange_vars_ctx A x y) <-> not_free_in_ctx (exchange_nat x y z) A .
Proof.
  split.
  - intro H.
    rewrite <- exchange_vars_ctx_inv with (A := A) (x := x) (y := y).
    apply exchange_vars_ctx_NF_aux.
    rewrite exchange_nat_inv.
    assumption.
  - apply exchange_vars_ctx_NF_aux.
Qed.

Lemma exchange_non_free_vars_ctx (A : list form) (x y : nat) :
  not_free_in_ctx x A -> not_free_in_ctx y A -> exchange_vars_ctx A x y = A.
Proof.
  induction A; intros NFCx NFCy.
  - reflexivity.
  - simpl exchange_vars_ctx.
    apply f_equal2.
    + apply exchange_non_free_vars; apply NFC_l_eq with (A := A); assumption.
    + apply IHA; apply NFC_l_eq with (s := a); assumption.
Qed.


Lemma exchange_vars_proof (A : list form) (s : form) (x y : nat) :
  nd A s -> nd (exchange_vars_ctx A x y) (exchange_vars s x y).
Proof.
  intro ND.
  revert x y.
  induction ND; intros m n.
  - apply Ass.
    apply in_map with (f := fun (s : form) => exchange_vars s m n).
    assumption.
  - apply Exp.
    apply IHND.
  - simpl exchange_vars.
    apply Iimp.
    apply IHND.
  - apply Eimp with (s := exchange_vars s m n).
    + apply IHND1.
    + apply IHND2.
  - simpl exchange_vars.
    apply Iconj.
    + apply IHND1.
    + apply IHND2. 
  - apply Econjr with (s := exchange_vars s m n).
    apply IHND.
  - apply Econjl with (t := exchange_vars t m n).
    apply IHND.
  - simpl exchange_vars.
    apply Idisjr.
    apply IHND.
  - simpl exchange_vars.
    apply Idisjl.
    apply IHND.
  - apply Edisj with (s := exchange_vars s m n) (t := exchange_vars t m n).
    + apply IHND1.
    + apply IHND2.
    + apply IHND3.
  - simpl exchange_vars.
    apply Ifor_all with (x := exchange_nat m n x).
    + apply exchange_vars_ctx_NF.
      rewrite exchange_nat_inv.
      assumption.
    + apply exchange_vars_NF.
      rewrite exchange_nat_inv.
      assumption.
    + rewrite <- exchange_vars_unbind.
      apply IHND.
  - rewrite exchange_vars_unbind.
    apply Efor_all.
    apply IHND.
  - apply Iexist with (x := exchange_nat m n x).
    rewrite <- exchange_vars_unbind.
    apply IHND.
  - apply Eexist with (x := exchange_nat m n x) (s := exchange_vars s m n).
    + apply exchange_vars_ctx_NF.
      rewrite exchange_nat_inv.
      assumption.
    + apply exchange_vars_NF.
      rewrite exchange_nat_inv.
      assumption.
    + apply exchange_vars_NF.
      rewrite exchange_nat_inv.
      assumption.
    + apply IHND1.
    + rewrite <- exchange_vars_unbind.
      apply IHND2.
Qed.


Fact Weak A B s :
  A |- s -> incl A B -> B |- s.
Proof.
  intro HA.
  revert B.
  induction HA; intros B AinB. 
  - apply Ass.
    apply (AinB s). assumption.
  - apply Exp.
    apply IHHA. assumption.
  - apply Iimp.
    apply IHHA.
    apply incl_cons. apply in_eq. apply incl_tl. assumption.
  - apply Eimp with (s := s).
    apply IHHA1. assumption.
    apply IHHA2. assumption.
  - apply Iconj.
    apply IHHA1. assumption.
    apply IHHA2. assumption.
  - apply Econjr with (s := s).
    apply IHHA. assumption.
  - apply Econjl with (t := t).
    apply IHHA. assumption.
  - apply Idisjr. 
    apply IHHA. assumption.
  - apply Idisjl.
    apply IHHA. assumption.
  - apply Edisj with (s := s) (t := t).
    + apply IHHA1. assumption.
    + apply IHHA2. assumption.
    + apply IHHA3. assumption.
  - destruct (NFC_existence (s::B)).
    apply Ifor_all with (x := x0).
    + apply NFC_l_eq with (s := s).
      assumption.
    + apply NFC_l_eq with (A := B).
      assumption.
    + rewrite <- exchange_nat_inv with (x := x) (y := x0) (z := x0).
      rewrite <- exchange_vars_inv with (s := s) (x := x) (y := x0).
      rewrite <- exchange_vars_ctx_inv with (A := B) (x := x) (y := x0).
      rewrite <- exchange_vars_unbind.
      apply exchange_vars_proof.
      rewrite exchange_nat_r.
      rewrite exchange_non_free_vars.
      * apply IHHA.
        rewrite <- exchange_non_free_vars_ctx with (A := A) (x := x) (y := x0).
          apply incl_map.
          assumption.
          assumption.
          apply NFC_incl with (B := s::B).
            apply incl_tl.
            assumption.
            assumption.
      * assumption.
      * apply NFC_in with (A := s::B).
          apply in_eq.
          assumption.
  - apply Efor_all.
    apply IHHA.
    assumption.
  - apply Iexist with (x := x).
    apply IHHA.
    assumption.
  - destruct (NFC_existence (s::t::B)).
    apply Eexist with (x := x0) (s := exchange_vars s x x0).
    + apply NFC_incl with (B := s::t::B).
      * apply incl_tl.
        apply incl_tl.
        apply incl_refl.
      * assumption.
    + apply exchange_vars_NF.
      rewrite exchange_nat_r.
      assumption.
    + apply NFC_in with (A := s::t::B).
      * apply in_cons.
        apply in_eq.
      * assumption.
    + rewrite <- exchange_vars_ctx_inv with (A := B) (x := x) (y := x0).
      rewrite <- exchange_vars_inv with (s := exist (exchange_vars s x x0)) (x := x) (y := x0).
      apply exchange_vars_proof.
      simpl exchange_vars.
      rewrite exchange_vars_inv.
      apply IHHA1.
      rewrite <- exchange_vars_ctx_inv with (A := A) (x := x) (y := x0).
      apply incl_map.
      rewrite exchange_non_free_vars_ctx.
      * assumption.
      * assumption.
      * apply NFC_incl with (B := s::t::B).
          apply incl_tl.
          apply incl_tl.
          assumption.
          assumption.
    + rewrite <- exchange_vars_ctx_inv with (A := B) (x := x) (y := x0).
      rewrite <- exchange_vars_inv with (s := unbind (exchange_vars s x x0) x0 ~> t) (x := x) (y := x0).
      apply exchange_vars_proof.
      simpl exchange_vars.
      rewrite exchange_vars_unbind.
      rewrite exchange_vars_inv.
      rewrite exchange_nat_r.
      rewrite exchange_non_free_vars.
      * apply IHHA2.
        rewrite <- exchange_vars_ctx_inv with (A := A) (x := x) (y := x0).
        apply incl_map.
        rewrite exchange_non_free_vars_ctx.
          assumption.
          assumption.
          apply NFC_incl with (B := s::t::B).
            apply incl_tl.
            apply incl_tl.
            assumption.
            assumption.
    * assumption.
    * apply NFC_in with (A := s::t::B).
        apply in_cons.
        apply in_eq.
        assumption.
Qed.

(** 2.b *)
Record HeytingAlgebra : Type :=
{ H : Type;
  leq : H -> H -> Prop;
  leq_refl s : leq s s;
  leq_trans s t u: (leq s t -> leq t u -> leq s u);
  bottom : H;
  meet : H -> H -> H;
  impl : H -> H -> H;
  join : H -> H -> H;
  inf : (H -> H) -> H;
  sup : (H -> H) -> H;
  leq_bottom u : leq bottom u;
  leq_meet s t u : ((leq u s) /\ (leq u t)) <-> leq u (meet s t);
  leq_impl s t u : (leq (meet s t) u) <-> leq s (impl t u);
  leq_join s t u : ((leq s u) /\ (leq t u)) <-> leq (join s t) u;
  leq_inf f u : leq u (inf f) <-> forall (s:H), leq u (f s);
  leq_sup f u : leq (sup f) u <-> exists (s:H), leq (f s) u
}.

Notation "s <= t" := (leq s t).

(** 2.c *)
Fixpoint eval {HA} (val : nat -> H HA) (f : form) :=
  match f with
  | free_var x => val x 
  | bound_var => 
  | bot => bottom HA 
  | imp s t => impl (eval val s) (eval val t)
  | conj s t => meet (eval val s) (eval val t)
  | disj s t => join (eval val s) (eval val t)
  | for_all s => 
  | exist s =>
  end.

(** 2.d *)
Fixpoint Meet_list {HA} (val : nat -> H HA) (l : list form) :=
  match l with
  | nil => impl (bottom HA) (bottom HA)
  | h::t => meet (eval val h) (Meet_list val t)
  end.

(** 2.e *)
Definition hent HA val A s := (@Meet_list HA val A) <= (@eval HA val s).

Lemma nd_soundHA HA val A s : nd A s -> @hent HA val A s.
Proof.
  intro H. induction H.
  - induction A. 
    + apply in_nil in H0. contradiction.
    + destruct H0.
      * unfold hent. simpl Meet_list. rewrite H0.
        apply (leq_meet (eval val s) (Meet_list val A) (meet (h:=HA) (eval val s) (Meet_list val A))).
        apply leq_refl.
      * unfold hent. simpl Meet_list.
        apply leq_trans with (t := Meet_list val A).
        apply (leq_meet (eval val a) (Meet_list val A) (meet (h:=HA) (eval val a) (Meet_list val A))).
        apply leq_refl.
        apply IHA. assumption.
  - unfold hent. apply leq_trans with (t := bottom HA).
    + assumption.
    + apply leq_bottom.
  - unfold hent. simpl eval.
    apply leq_impl.
    unfold hent in IHnd.
    simpl Meet_list in IHnd.
    apply leq_trans with (t := meet (h:=HA) (eval val s) (Meet_list val A)).
    + apply leq_meet. split;
      apply (leq_meet (Meet_list val A) (eval val s) (meet (h:=HA) (Meet_list val A) (eval val s)));
      apply leq_refl.
    + assumption.
  - unfold hent.
    apply leq_trans with (t := meet (h:=HA) (Meet_list val A) (eval val s)).
    + apply leq_meet. split.
      * apply leq_refl.
      * assumption.
    + apply leq_impl. assumption.
  - apply leq_meet. split; assumption.
  - apply leq_meet in IHnd. destruct IHnd. assumption.
  - apply leq_meet in IHnd. destruct IHnd. assumption.
Qed.

(** 2.f *)

Fixpoint revert A s :=
  match A with
  |[] => s
  |a::A => (revert A (a ~> s))
  end.

Lemma revert_correct A s :
  A |- s <-> [] |- revert A s.
Proof.
  split; revert s. 
  - induction A; intros s H.
    + unfold revert. assumption.
    + simpl. apply IHA.
      apply Iimp. assumption.
  - induction A; intros s H.
    + unfold revert in H. assumption.
    + apply Eimp with (s := a). 
      * apply Ass. apply in_eq.
      * apply Weak with (A := A).
        apply IHA. apply H.
        apply incl_tl. apply incl_refl.
Qed.

(** 2.g *)
Definition HA_leq := fun s t => [] |- s ~> t.
Definition HA_bot := bot.
Definition HA_impl s t := imp s t. 
Definition HA_meet s t := conj s t.

Lemma HA_leq_refl (s : form) :
  HA_leq s s.
Proof.
  unfold HA_leq.
  apply Iimp.
  apply Ass.
  apply in_eq.
Qed.

Lemma HA_leq_trans (s t u : form) :
  HA_leq s t -> HA_leq t u -> HA_leq s u.
Proof.
  unfold HA_leq.
  intros H1 H2.
  apply Iimp.
  apply Eimp with (s := t).
  - apply Eimp with (s := s).
    + apply Ass. apply in_eq.
    + apply Weak with (A := []). 
      * assumption. 
      * apply incl_tl. apply incl_refl.
  - apply Weak with (A := []).
    + assumption.
    + apply incl_tl. apply incl_refl.
Qed.

Lemma HA_leq_bottom (u : form) :
  HA_leq HA_bot u.
Proof.
  unfold HA_leq. unfold HA_bot.
  apply Iimp.
  apply Exp.
  apply Ass. apply in_eq.
Qed.

Lemma HA_leq_meet (s t u : form) :
  HA_leq u s /\ HA_leq u t <-> HA_leq u (HA_meet s t).
Proof.
  unfold HA_leq. unfold HA_meet.
  split; intro H.
  - destruct H. 
    apply Iimp. apply Iconj.
    + apply Eimp with (s := u).
      * apply Ass. apply in_eq.
      * apply Weak with (A := []).
        assumption.
        apply incl_tl. apply incl_refl.
    + apply Eimp with (s := u).
      * apply Ass. apply in_eq.
      * apply Weak with (A := []).
        assumption.
        apply incl_tl. apply incl_refl.
  - split.
    + apply Iimp. 
      apply Econjl with (t := t).
      apply Eimp with (s := u).
      * apply Ass. apply in_eq.
      * apply Weak with (A := []).
        assumption.
        apply incl_tl. apply incl_refl.
    + apply Iimp. 
      apply Econjr with (s := s).
      apply Eimp with (s := u).
      * apply Ass. apply in_eq.
      * apply Weak with (A := []).
        assumption.
        apply incl_tl. apply incl_refl.
Qed.

Lemma HA_leq_impl (s t u : form) :
  (HA_leq (HA_meet s t) u) <-> HA_leq s (HA_impl t u).
Proof.
  unfold HA_leq. unfold HA_meet. unfold HA_impl.
  split; intro H.
  - apply Iimp. apply Iimp. 
    apply Eimp with (s := conj s t).
    + apply Iconj.
      * apply Ass. apply in_cons. apply in_eq.
      * apply Ass. apply in_eq.
    + apply Weak with (A := []).
      * assumption.
      * apply incl_tl. apply incl_tl. apply incl_refl.
  - apply Iimp.
    apply Eimp with (s := t).
    + apply Econjr with (s := s).
      apply Ass. apply in_eq.
    + apply Eimp with (s := s).
      * apply Econjl with (t := t).
        apply Ass. apply in_eq.
      * apply Weak with (A := []).
        assumption.
        apply incl_tl. apply incl_refl.
Qed.

Definition HA_formula : HeytingAlgebra :=
{| H := form;
  leq := HA_leq;
  leq_refl := HA_leq_refl;
  leq_trans := HA_leq_trans;
  bottom := HA_bot;
  meet := HA_meet;
  impl := HA_impl;
  leq_bottom := HA_leq_bottom;
  leq_meet := HA_leq_meet;
  leq_impl := HA_leq_impl
|}.

(** 2.h *)
Lemma eval_is_id (s : form) :
  eval (HA:=HA_formula) var s = s.
Proof.
  induction s.
  - reflexivity.
  - reflexivity.
  - simpl eval. rewrite IHs1. rewrite IHs2. reflexivity.
  - simpl eval. rewrite IHs1. rewrite IHs2. reflexivity.
Qed.

(** 2.i *)
(*Lemma Heyting_completeness *)

Lemma revert_HA (HA : HeytingAlgebra) (val : nat -> H HA) A s :
  hent val A s <-> hent val [] (revert A s).
Proof.
  split; revert s; induction A; intros s H.
  - assumption.
  - simpl.
    apply IHA.
    apply leq_impl.
    apply leq_trans with (t := meet (eval val a) (Meet_list val A)).
    + apply leq_meet; split; 
      apply (leq_meet (Meet_list val A) (eval val a) (meet (Meet_list val A) (eval val a)));
      apply leq_refl.
    + assumption.
  - assumption.
  - apply leq_trans with (t := meet (Meet_list val A) (eval val a)).
    + apply leq_meet; split;
      apply (leq_meet (eval val a) (Meet_list val A) (meet (eval val a) (Meet_list val A)));
      apply leq_refl.
    + apply leq_impl.
      apply IHA with (s := a ~> s).
      assumption.
Qed.

Proposition nd_completeHA A s :
  (forall (HA : HeytingAlgebra) (V : nat -> H HA), hent V A s) -> nd A s.
Proof.
  intro H.
  apply revert_correct.
  apply Eimp with (s := bot ~> bot).
  - apply Iimp. apply Ass. apply in_eq.
  - specialize H with (HA := HA_formula) (V := var).
    apply revert_HA in H.
    simpl in H.
    rewrite eval_is_id in H.
    assumption.
Qed.

Theorem HA_iff_nd A s:
(forall (HA : HeytingAlgebra) (V : nat -> H HA), hent V A s) <-> nd A s.
Proof.
  split.
  - apply nd_completeHA.
  - intros H HA V.
    apply nd_soundHA.
    assumption.
Qed.















