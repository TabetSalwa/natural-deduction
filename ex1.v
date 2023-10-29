Require Import List.
Import ListNotations.

Inductive form : Type :=
| var ( x : nat) | bot | imp ( s t : form).

Print In.
Print incl.

Notation "s ~> t" := (imp s t) ( at level 51, right associativity).
Notation neg s := ( imp s bot).
Reserved Notation "A |- s" (at level 70).

(** 1.1.a *)
Inductive nd : list form -> form -> Prop :=
  |Ass A s : (In s A) -> nd A s
  |Exp A s : nd A bot -> nd A s
  |Iimp A s t : nd (s::A) t -> nd A (s ~> t)
  |Eimp A s t : nd A s -> nd A (s ~> t) -> nd A t.

Notation "A |- s" := (nd A s) ( at level 70).

Tactic Notation "Ass" integer(n) :=
  apply Ass; do n (apply in_cons); apply in_eq.

(** 1.1.b *)
Definition statement1 (A : list form) (s : form) : A |- s ~> s :=
  Iimp A s s (Ass (s::A) s (in_eq s A)).

Definition statement2 (A : list form) (s : form) : (s::A) |- neg (neg s) :=
  Iimp (s::A) (neg s) bot 
  (Eimp (neg s::s::A) s bot 
  (Ass (neg s::s::A) s (in_cons (neg s) s (s::A) (in_eq s A)))
  (Ass (neg s::s::A) (neg s) (in_eq (neg s) (s::A)))).

Definition statement3 : [neg (neg bot)] |- bot :=
  (Eimp [neg (neg bot)] (neg bot) bot
  (Iimp [neg (neg bot)] bot bot 
  (Ass [bot;neg (neg bot)] bot (in_eq bot [neg (neg bot)])))
  (Ass [neg (neg bot)] (neg (neg bot)) (in_eq (neg (neg bot)) []))).

(** 1.1.c *)
Fact Weak A B s :
  A |- s -> incl A B -> B |- s.
Proof.
  intro HA.
  revert B.
  induction HA; intros B AinB.
  - apply (Ass B s).
    apply (AinB s). assumption.
  - apply (Exp B s).
    apply IHHA. assumption.
  - apply (Iimp B s t).
    apply IHHA.
    apply incl_cons. apply in_eq. apply incl_tl. assumption.
  - apply (Eimp B s t).
    apply IHHA1. assumption.
    apply IHHA2. assumption.
Qed.

(** 1.1.d *)
Inductive ground : form -> Prop :=
  |Gnd_bot : ground bot
  |Gnd_imp s t : ground s -> ground t -> ground (s ~> t).

Fixpoint ground_truth (s : form) : bool :=
  match s with
  |var x => false
  |bot => false
  |s ~> t => implb (ground_truth s) (ground_truth t)
end.

Lemma ground_dec s :
  ground s -> ((ground_truth s = true -> ([] |- s)) /\ (ground_truth s = false -> ([] |- neg s))).
Proof.
  intro H.
  induction H.
  - split; intro H.
    + discriminate H.
    + apply Iimp.
      Ass 0.
  - destruct IHground1, IHground2.
    split; simpl ground_truth; intro H5.
    + destruct (Bool.bool_dec (ground_truth s) true).
      * apply Iimp.
        apply (Weak [] _ _).
        apply H3.
        rewrite e in H5.
        assumption.
        intro a.
        intro H6.
        inversion H6.
      * apply Iimp.
        apply Exp.
        apply (Eimp _ s _).
        Ass 0.
        apply (Weak [] _ _).
        apply H2.
        apply Bool.not_true_iff_false.
        assumption.
        intro a.
        intro H6.
        inversion H6.
    + destruct (Bool.bool_dec (ground_truth s) true).
      * apply Iimp.
        eapply (Eimp _ _ _).
        eapply (Eimp _ _ _).
        apply (Weak [] _ _).
        apply H1.
        assumption.
        intro a.
        intro H6.
        inversion H6.
        Ass 0.
        apply (Weak [] _ _).
        apply H4.
        rewrite e in H5.
        assumption.
        intro a.
        intro H6.
        inversion H6.
      * apply Bool.not_true_iff_false in n.
        rewrite n in H5.
        inversion H5.
Qed.

Fact ground_decidable s :
  ground s -> ([] |- s) + ([] |- neg s).
Proof.
  intro H.
  destruct (Bool.bool_dec (ground_truth s) true).
  - left.
    apply ground_dec; assumption.
  - right.
    apply ground_dec.
    assumption.
    apply Bool.not_true_iff_false.
    assumption.
Qed.

(** 1.2.a *)
Inductive ndc : list form -> form -> Prop :=
  |Assc A s : In s A -> ndc A s
  |Enegc A s : ndc (neg s::A) bot -> ndc A s
  |Iimpc A s t : ndc (s::A) t -> ndc A (imp s t)
  |Eimpc A s t : ndc A s -> ndc A (imp s t) -> ndc A t.

Notation "A |-c s" := (ndc A s) ( at level 70).

(** 1.2.b *)
Definition statement1c (A : list form) (s : form) : A |-c (neg (neg s)) ~> s :=
  Iimpc A (neg (neg s)) s
  (Enegc ((neg (neg s))::A) s
  (Eimpc (neg s::(neg (neg s))::A) (neg s) bot
  (Assc (neg s::(neg (neg s))::A) (neg s) (in_eq (neg s) ((neg (neg s))::A)))
  (Assc (neg s::(neg (neg s))::A) (neg (neg s)) (in_cons (neg s) (neg (neg s)) ((neg (neg s))::A) (in_eq (neg (neg s)) A)
)))).

(** 1.2.c *)
Lemma Weakc A B s :
  A |-c s -> incl A B -> B |-c s.
Proof.
  intro HA.
  revert B.
  induction HA; intros B AinB.
  - apply (Assc B s).
    apply (AinB s). assumption.
  - apply (Enegc B s).
    apply IHHA.
    apply incl_cons. apply in_eq. apply incl_tl. assumption.
  - apply (Iimpc B s t).
    apply IHHA.
    apply incl_cons. apply in_eq. apply incl_tl. assumption.
  - apply (Eimpc B s t).
    apply IHHA1. assumption.
    apply IHHA2. assumption.
Qed.

(** 1.2.d *)
Lemma Implication A s :
  A |- s -> A |-c s.
Proof.
  intro I.
  induction I.
  - apply (Assc A s). assumption.
  - apply (Enegc A s). 
    apply (Weakc A (neg s::A) bot).
    + assumption.
    + apply incl_tl. apply incl_refl.
  - apply (Iimpc A s t).
    apply IHI.
  - apply (Eimpc A s t); assumption.
Qed.

(** 1.2.e *)
Fixpoint trans (t s : form) : form :=
  match s with
  | var x => (var x ~> t) ~> t
  | bot => t
  | imp f1 f2  => imp (trans t f1) (trans t f2)
  end.

(** 1.2.f *) 
Lemma imp_4_2 A (s t : form) :
  A |- ((((s ~> t) ~> t) ~> t) ~> t) ~> ((s ~> t) ~> t).
Proof.
  apply Iimp.
  apply Iimp.
  apply (Eimp _ (((s ~> t) ~> t) ~> t) t).
  - apply Iimp.
    apply (Eimp _ (s ~> t) t).
    + Ass 1.
    + Ass 0.
  - Ass 1.
Qed.

Lemma DNE_Friedman A s t :
  A |- ((trans t s ~> t) ~> t) ~> (trans t s).
Proof.
  revert A.
  induction s; intro A; simpl trans.
  - apply (imp_4_2 A (var x) t).
  - apply Iimp.
    apply (Eimp _ (t ~> t) t).
    + apply Iimp.
      Ass 0.
    + Ass 0.
  - apply Iimp.
    apply Iimp.
    apply (Eimp _ ((trans t s2 ~> t) ~> t) _).
    + apply Iimp.
      apply (Eimp _ ((trans t s1 ~> trans t s2) ~> t) _).
      * apply Iimp.
        apply (Eimp _ (trans t s2) t).
        apply (Eimp _ (trans t s1) (trans t s2));
        [Ass 2 | Ass 0 ].
        Ass 1.
      * Ass 2.
   + apply IHs2.
Qed.

(** 1.2.g *)
Lemma Friedman A s t :
  A |-c s -> map (trans t) A |- trans t s.
Proof.
  intro C.
  induction C.
  - apply Ass. apply in_map. assumption.
  - apply (Eimp _ ((trans t s ~> t) ~> t) _).
    + apply Iimp. assumption.
    + apply DNE_Friedman.
  - simpl trans.
    apply Iimp.
    assumption.
  - apply (Eimp _ (trans t s) _); assumption.
Qed.

(** 1.2.h *)
Lemma trans_ground (s : form) :
  ground s -> trans bot s = s.
Proof.
  intro H.
  induction H.
  - reflexivity.
  - simpl trans.
    congruence.
Qed.

Lemma ground_truths s:
  ground s -> ([] |- s <-> [] |-c s).
Proof.
  intro H.
  split.
  - apply Implication.
  - intro H1.
    rewrite <- trans_ground.
    + apply (Friedman [] _ _).
      assumption.
    + assumption.
Qed.

(** 1.2.i *)

(*
Intuitionistic natural deduction is *not* consistent if and only if [] |- bot.
Classical natural deduction is *not* consistent if and only if [] |-c bot. 
Since bot is a ground formula, we have shown that these two notions are equivalent.
*)

(** 1.3 *)
Inductive tval := ff | nn | tt.

Definition leq a b : bool :=
  match a, b with
  | ff, _ => true
  | nn, nn => true
  | nn, tt => true
  | tt, tt => true
  | _, _ => false
  end.

Notation "a <= b" := (leq a b).

Definition impl a b : tval :=
  if a <= b then tt else b.

Fixpoint eva alpha (s : form) : tval :=
  match s with
  | var x => alpha x
  | bot => ff
  | imp s1 s2 => impl (eva alpha s1) (eva alpha s2)
  end.

Fixpoint evac alpha (A : list form) : tval :=
  match A with
  | nil => tt
  | s::A' => if eva alpha s <= evac alpha A' then eva alpha s else evac alpha A'
  end.

Notation leb alpha A s := (evac alpha A <= eva alpha s = true).

(**1.3.a**)
Lemma leq_trans a b c :
  (a <= b = true) -> (b <= c = true) -> (a <= c = true).
Proof.
  case a.
  - case c; reflexivity.
  - case b. 
    + intro H. inversion H.
    + intros H H1. assumption.
    + case c; auto. 
  - case b; intros; (inversion H || assumption).
Qed.

Theorem nd_sound alpha A s :
  A |- s -> leb alpha A s.
Proof.
  intro H.
  induction H.
  - induction A.
    inversion H.
    destruct H.
    + rewrite H.
      simpl evac.
      case (eva alpha s); case (evac alpha A); reflexivity.
    + simpl evac.
      apply (leq_trans _ (evac alpha A) _).
      case (eva alpha a); case (evac alpha A); reflexivity.
      apply IHA.
      assumption.
  - apply (leq_trans _ ff _).
    + assumption.
    + case (eva alpha s); reflexivity.
  - revert IHnd.
    simpl.
    case (evac alpha A); case (eva alpha s); case (eva alpha t);
    solve [reflexivity|intro H1; inversion H1].
  - revert IHnd2. revert IHnd1. 
    simpl.
    case (evac alpha A); case (eva alpha s); case (eva alpha t);
    solve [reflexivity | intro H1; inversion H1 | intros H1 H2; inversion H2].
Qed.

(**1.3.b**)
Corollary nd_DN x :
  ~ [] |- (neg (neg (var x))) ~> (var x).
Proof.
  intro I.
  apply (nd_sound (fun n => nn) [] _) in I.
  simpl in I.
  discriminate I.
Qed.


(**1.3.c**)
Corollary nd_consistent :
  ~ [] |- bot.
Proof.
  intro I.
  apply (nd_sound (fun n => nn) [] _) in I. 
  simpl in I.
  discriminate I.
Qed.

(**1.3.d**)
Corollary ndc_consistent :
  ~ [] |-c bot.
Proof.
  intro I.
  apply nd_consistent.
  apply ground_truths.
  constructor.
  assumption.
Qed.



















