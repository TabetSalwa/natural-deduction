Set Implicit Arguments.
Unset Strict Implicit.
Require Import List.
Import ListNotations.

Inductive form : Type :=
| var ( x : nat) 
| bot 
| imp ( s t : form)
| conj ( s t : form).

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
  |Econjl A s t : nd A (conj s t) -> nd A s.

Notation "A |- s" := (nd A s) ( at level 70).

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
  leq_bottom u : leq bottom u;
  leq_meet s t u: ((leq u s) /\ (leq u t)) <-> leq u (meet s t);
  leq_impl s t u: (leq (meet s t) u) <-> leq s (impl t u)
}.

Notation "s <= t" := (leq s t).

(** 2.c *)
Fixpoint eval {HA} (val : nat -> H HA) (f : form) :=
  match f with
  | var x => val x 
  | bot => bottom HA 
  | imp s t => impl (eval val s) (eval val t)
  | conj s t => meet (eval val s) (eval val t)
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















