Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

(** 3.a *)
Inductive form : Type :=
| var (x : nat)
| bot
| imp (s t : form)
| conj (s t : form)
| disj (s t : form).

(** 3.b *)
Fixpoint reflection (f : form) (val : nat -> Z) :=
  match f with
  | var x => val x
  | bot => Z0
  | imp s t => let s' := reflection s val in
               let t' := reflection t val in
               s' * t'- s' + 1
  | conj s t => (reflection s val) * (reflection t val)
  | disj s t => let s' := reflection s val in
                let t' := reflection t val in
                s' + t' - s' * t'
  end.

Fixpoint evaluation (f : form) (val : nat -> bool) : bool :=
  match f with
  | var x => val x
  | bot => false
  | imp s t => implb (evaluation s val) (evaluation t val)
  | conj s t => andb (evaluation s val) (evaluation t val)
  | disj s t => orb (evaluation s val) (evaluation t val)
  end.

Theorem eval_is_refl : forall (f : form) (val : nat -> bool),
  (if evaluation f val then 1%Z else 0%Z) = 
  reflection f (fun n => if val n then 1%Z else 0%Z).
Proof.
  intros f val.
  induction f;
  solve [unfold evaluation, reflection; reflexivity |
         simpl; rewrite <- IHf1; rewrite <- IHf2;
         destruct (evaluation f1 val); destruct (evaluation f2 val); reflexivity].
Qed.

Close Scope Z_scope. 

(** 3.c *)
Ltac list_add a l :=
  let rec aux a l n :=
    lazymatch l with
    | [] => constr:((n, cons a l))
    | a :: _ => constr:((n,l))
    | ?x :: ?l =>
      match aux a l (S n) with
      | (?n, ?l) => constr:((n, cons x l))
      end
    end in
  aux a l 0.

Ltac read_term f l :=
  lazymatch f with
  | true => constr:((imp bot bot, l))
  | false => constr:((bot, l))
  | negb ?x =>
    match read_term x l with
    | (?x', ?l') => constr:((imp x' bot, l'))
    end
  | andb ?x ?y =>
    match read_term x l with
    | (?x', ?l') =>
      match read_term y l' with
      | (?y', ?l'') => constr:((conj x' y', l''))
      end
    end
  | orb ?x ?y => 
    match read_term x l with
    | (?x', ?l') => 
      match read_term y l' with
      | (?y', ?l'') => constr:((disj x' y', l''))
      end
    end
  | implb ?x ?y =>
    match read_term x l with
    | (?x', ?l') => 
      match read_term y l' with
      | (?y', ?l'') => constr:((imp x' y', l''))
      end
    end
  | _ =>
    match list_add f l with 
      | (?n, ?l') => constr:((var n, l'))
    end
  end.

Ltac reify f :=
  read_term f (@nil bool).

Ltac reify2 f1 f2 :=
  match reify f1 with 
  | (?f1', ?l) =>
    match read_term f2 l with 
    | (?f2', ?l') => constr:(((f1', f2'), l'))
    end 
  end.


Require Import Lia.
Open Scope Z_scope.

Definition bool_to_Z (b:bool) :=
  if b then 1%Z else 0%Z.

Lemma true_Z :
  bool_to_Z true = 1%Z.
Proof.
  reflexivity.
Qed.

Lemma false_Z :
  bool_to_Z false = 0%Z.
Proof.
  reflexivity.
Qed.

Lemma and_Z (b1 b2 : bool) :
  bool_to_Z (andb b1 b2) = (bool_to_Z b1) * (bool_to_Z b2).
Proof.
  case b1; case b2; reflexivity.
Qed.

Lemma or_Z (b1 b2 : bool) :
  bool_to_Z (orb b1 b2) = (bool_to_Z b1) + (bool_to_Z b2) - (bool_to_Z b1) * (bool_to_Z b2).
Proof.
  case b1; case b2; reflexivity.
Qed.

Lemma neg_Z (b : bool) :
  bool_to_Z (negb b) = 1 - (bool_to_Z b).
Proof.
  case b; reflexivity.
Qed.

Lemma bool_to_Z_inj (b1 b2 : bool) :
  bool_to_Z b1 = bool_to_Z b2 -> b1 = b2.
Proof.
  case b1; case b2; intro H;
  solve [reflexivity | discriminate H].
Qed.

Lemma imp_Z (b1 b2 : bool) :
  bool_to_Z (implb b1 b2) = (bool_to_Z b1) * (bool_to_Z b2) - (bool_to_Z b1) + 1.
Proof.
  case b1; case b2; reflexivity.
Qed.

Close Scope Z_scope.

Ltac rewrite_bool f :=
  lazymatch f with
  | conj ?a ?b => try rewrite and_Z; rewrite_bool a; rewrite_bool b
  | disj ?a ?b => try rewrite or_Z; rewrite_bool a; rewrite_bool b
  | imp bot bot => try rewrite true_Z
  | imp ?a bot => try rewrite neg_Z; rewrite_bool a  
  | imp ?a ?b => try rewrite imp_Z; rewrite_bool a; rewrite_bool b
  | bot => try rewrite false_Z
  | var ?n => idtac
  end.

Ltac eq_reflection :=
  intros;
  match goal with 
  |[ |- ?x = ?y] => 
    match reify2 x y with
    | ((?x', ?y'), ?l) =>
      apply bool_to_Z_inj;
      rewrite_bool x';
      rewrite_bool y'
    end
  end;
  lia.


Goal forall a b c, orb (negb a) (orb (negb b) (andb c true)) = negb (andb a (andb b (negb c))).
Proof.
  eq_reflection.
Qed.

Goal forall a b, andb a b = andb b a.
Proof.
  eq_reflection.
Qed.

Goal forall a, negb (negb (negb a)) = negb a.
Proof.
  eq_reflection.
Qed.

Goal forall a b c, implb (andb a b) c = implb (andb b a) c.
Proof.
  eq_reflection.
Qed.

Goal forall a b, orb (andb b (andb a b)) (andb a b) = andb b a.
Proof.
  Fail eq_reflection.
Abort.

Goal forall a b c d, andb a (andb (andb b b) (implb c d)) = andb a (andb b (implb c d)).
Proof.
  Fail eq_reflection.
Abort. 

Goal forall a b c, implb (andb (negb b) (orb a c)) a = negb (andb (negb a) (andb (negb b) c)).
Proof.
  Fail eq_reflection.
Abort.











