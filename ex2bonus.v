Set Implicit Arguments.
Unset Strict Implicit.
Require Import List.
Import ListNotations.
Require Import Arith.EqNat.
Require Import Arith.Le.

(** Defining some functions on natural integers **)

Definition change_val (A : Type) (f : nat -> A) (x : nat) (a : A) : nat -> A :=
  fun (y : nat) => if Nat.eqb x y then a else f y.

Lemma change_val_refl (A : Type) (f : nat -> A) (x : nat) (a : A) :
  change_val f x a x = a.
Proof.
  unfold change_val.
  rewrite Nat.eqb_refl with (x := x).
  reflexivity.
Qed.

Fixpoint remove_nat (A : Type) (x : nat) (f : nat -> A) (offset : nat) (default : A) (y : nat) : A :=
  match x with
  | 0 => match y with
         | 0 => default
         | S y => f (offset + y)
         end
  | S x => match y with
         | 0 => f offset
         | S y => remove_nat x f (S offset) default y
         end
  end.

Lemma remove_nat_gt (A : Type) (x : nat) (f : nat -> A) (default : A) (y : nat) :
  x <= y -> remove_nat x f 0 default (S y) = f y.
Proof.
  remember (f y) as fy.
  rewrite <- Nat.add_0_l with (n := y) in Heqfy.
  rewrite Heqfy.
  clear fy Heqfy.
  generalize 0 as offset.
  revert y.
  induction x; intro y.
  - destruct y; reflexivity.
  - destruct y; intros offset Hle.
    + contradiction (Nat.nle_succ_0 x Hle).
    + rewrite <- Nat.add_succ_comm with (n := offset) (m := y).
      apply IHx.
      apply le_S_n.
      apply Hle.
Qed.

Lemma remove_nat_lt (A : Type) (x : nat) (f : nat -> A) (default : A) (y : nat) :
  y < x -> remove_nat x f 0 default y = f y.
Proof.
  remember (f y) as fy.
  rewrite <- Nat.add_0_l with (n := y) in Heqfy.
  rewrite Heqfy.
  clear fy Heqfy.
  generalize 0 as offset.
  revert y.
  induction x; intro y.
  - intros offset Hlt.
    contradiction (Nat.nle_succ_0 y Hlt).
  - destruct y; intros offset Hle.
    + rewrite Nat.add_0_r with (n := offset).
      reflexivity.
    + rewrite <- Nat.add_succ_comm with (n := offset) (m := y).
      apply IHx.
      apply le_S_n.
      apply Hle.
Qed.

Lemma remove_nat_eq (A : Type) (x : nat) (f : nat -> A) (default : A) :
  remove_nat x f 0 default x = default.
Proof.
  generalize 0 as offset.
  induction x; intro offset.
  - reflexivity.
  - apply IHx.
Qed.

Definition exchange_nat (x y z : nat) : nat :=
  if Nat.eqb z x then y else if Nat.eqb z y then x else z.

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

(** Encoding definable subsets of A as elements of type A -> Prop **)

Inductive finite_set (A : Type) (l : list A) : A -> Prop :=
  | Finite_set : forall (a : A), In a l -> finite_set l a.

Inductive fun_image (A : Type) (f : A -> A) (P : A -> Prop) : A ->  Prop :=
  | Fun_image : forall (a : A), P a -> fun_image f P (f a).


(** Implementation of vect A n et fin n **)

Inductive fin : nat -> Set :=
  | Zero : forall (n : nat), fin (S n)
  | Succ : forall (n : nat), fin n -> fin (S n).

Inductive vect (A : Type) : nat -> Type :=
  | Vnil : vect A 0
  | Vcons : forall (n : nat), A -> vect A n -> vect A (S n).

Fixpoint nat_to_fin (n m : nat) : m < n ->  fin n :=
  match n with
  | 0 => fun p => except ((Nat.nle_succ_0 m) p)
  | S n => match m with
           | 0 => fun p => Zero n
           | S m => fun p => Succ (nat_to_fin (le_S_n (S m) n p))
           end
  end.

Fixpoint fin_incl (n m : nat) : m <= n -> fin m -> fin n :=
  match n with
  | 0 => match m with
         | 0 => fun _ t => t
         | S m => fun p _ => except (Nat.nle_succ_0 m p)
         end
  | S n => match m with
           | 0 => fun _ (t : fin 0) => match t in fin m return (match m with 0 => fin (S n) | S _ => unit end) with
                             | Zero _ => tt
                             | Succ _ => tt
                             end
           | S m => fun p t => let t := match t in fin (S m) return option (fin m) with
                               | Zero _ => None
                               | Succ t => Some t
                               end in match t with
                               | None => Zero n
                               | Some t => Succ (fin_incl (le_S_n m n p) t)
                               end
           end
  end.


Fixpoint vect_proj (A : Type) (n m : nat) : m <= n -> vect A n -> vect A m :=
  match n with
  | 0 => match m with
         | 0 => fun _ v => v
         | S m => fun p _ => match (fin_incl p (Zero m)) in fin n0 return (match n0 with 0 => vect A (S m) | S _ => unit end) with
                             | Zero _ => tt
                             | Succ _ => tt
                             end
         end
  | S n => match m with
           | 0 => fun _ _ => Vnil A
           | S m => fun p v => let (x,v) := (match v in vect _ (S n) return A * vect A n with
                               | Vcons x v => (x,v)
                               end) in Vcons x (vect_proj (le_S_n m n p) v)
           end
  end.

Fixpoint Vnth (A : Type) (n : nat) (t : fin n) : vect A n -> A :=
  match t with
  | Zero n => fun v => match v with Vcons x _ => x end
  | Succ t => fun v => Vnth t (match v with Vcons _ v => v end)
  end.


Lemma vect_proj_vnth (A : Type) (n m : nat) (p : m <= n) (t : fin m) (v : vect A n) :
  Vnth t (vect_proj p v) = Vnth (fin_incl p t) v.
Proof.
  revert m t p.
  induction v; intros m t.
  - destruct t; intro p; contradiction (Nat.nle_succ_0 n p).
  - destruct t; intro p.
    + reflexivity.
    + apply IHv.
Qed.

Fixpoint make_vect (A : Type) (n : nat) (x : A) : vect A n :=
  match n with
  | 0 => Vnil A
  | S n => Vcons x (make_vect n x)
  end.

Fixpoint vect_app (A : Type) (n m : nat) (a0 : A) : m <= n -> vect A m -> vect A n :=
  match n with
  | 0 => match m with
         | 0 => fun _ _ => Vnil A
         | S m => fun (p : m < 0) _ => match fin_incl p (Zero m) in fin n0 return (match n0 with 0 => vect A 0 | S _ => unit end) with
                                          | Zero _ => tt
                                          | Succ _ => tt
                                          end
         end
  | S n => match m with
           | 0 => fun _ _ => make_vect (S n) a0
           | S m => fun (p : S m <= S n) (v : vect A (S m)) => let (x,v') := match v in vect _ (S m) return A * vect A m with
                                                                             | Vcons x v => (x,v)
                                                                             end in Vcons x (vect_app a0 (le_S_n m n p) v')
           end
  end.

Lemma vect_proj_app_inv (A : Type) (n m : nat) (a0 : A) (p : m <= n) (v : vect A m) :
  vect_proj p (vect_app a0 p v) = v.
Proof.
  revert m p v.
  induction n; intros m p v.
  - induction v.
    + reflexivity.
    + contradiction (Nat.nle_succ_0 n p).
  - induction v.
    + reflexivity.
    + simpl.
      apply f_equal2 with (f := @Vcons A n0).
      * reflexivity.
      * apply IHn.
Qed.

Fixpoint insert (A : Type) (n m : nat) (a0 : A) : m <= n -> vect A n -> vect A (S n) :=
  match m with
  | 0 => fun _ => Vcons a0
  | S m => match n with
           | 0 => fun p _ => match fin_incl p (Zero m) in fin n0 return (match n0 with 0 => vect A 1 | S _ => unit end) with
                             | Zero _ => tt
                             | Succ _ => tt
                             end
           | S n => fun p v => let (x,v') := match v in vect _ (S n) return A * vect A n with
                                           | Vcons x v => (x,v)
                                           end in Vcons x (insert a0 (le_S_n m n p) v')
           end
  end.

Lemma nat_to_fin_proof_irrelevance (n m : nat) (p q : m < n) :
  nat_to_fin p = nat_to_fin q.
Proof.
  revert m p q.
  induction n; intro m.
  - intro p.
    contradiction (Nat.nle_succ_0 m p).
  - induction m; intros p q.
    + reflexivity.
    + simpl nat_to_fin.
      apply f_equal.
      apply IHn.
Qed.

Lemma insert_proof_irrelevance (A : Type) (n m : nat) (a0 : A) (p q : m <= n) :
  insert a0 p = insert a0 q.
Proof.
  revert m p q.
  induction n.
  - destruct m; intros p q.
    + reflexivity.
    + contradiction (Nat.nle_succ_0 m p).
  - destruct m; intros p q.
    + reflexivity.
    + simpl.
      rewrite IHn with (p := le_S_n m n p) (q := le_S_n m n q).
      reflexivity.
Qed.

Lemma insert_vnth_lt (A : Type) (n m o : nat) (a0 : A) (p : m <= n) (q : o < m) (v : vect A n) :
  Vnth (nat_to_fin (le_S (S o) n (Nat.le_trans (S o) m n q p))) (insert a0 p v) = Vnth (nat_to_fin (Nat.le_trans (S o) m n q p)) v.
Proof.
  revert m p o q.
  induction v; intro m.
  - intros p o q.
    contradiction (Nat.nle_succ_0 o (Nat.le_trans (S o) m 0 q p)).
  - destruct m; intros p o q.
    + contradiction (Nat.nle_succ_0 o q).
    + destruct o.
      * reflexivity.
      * simpl insert.
        simpl nat_to_fin.
        simpl Vnth.
        change (match o as m1 return (m1 < S n -> fin (S n)) with
      | 0 => fun _ : 0 < S n => Zero n
      | S m0 => fun p0 : S m0 < S n => Succ (nat_to_fin (n:=n) (m:=m0) (le_S_n (S m0) n p0))
      end (le_S_n (S o) (S n) (le_S (S (S o)) (S n) (Nat.le_trans (S (S o)) (S m) (S n) q p)))) with (nat_to_fin (le_S_n (S o) (S n) (le_S (S (S o)) (S n) (Nat.le_trans (S (S o)) (S m) (S n) q p)))).
        rewrite nat_to_fin_proof_irrelevance with (p := le_S_n (S o) (S n) (le_S (S (S o)) (S n) (Nat.le_trans (S (S o)) (S m) (S n) q p))) (q := le_S (S o) n (Nat.le_trans (S o) m n (le_S_n (S o) m q) (le_S_n m n p))).
        rewrite nat_to_fin_proof_irrelevance with (p := le_S_n (S o) n (Nat.le_trans (S (S o)) (S m) (S n) q p)) (q := Nat.le_trans (S o) m n (le_S_n (S o) m q) (le_S_n m n p)).
        apply IHv.
Qed.

Lemma insert_vnth_gt (A : Type) (n m o : nat) (a0 : A) (p : m <= o) (q : o < n) (v : vect A n) :
  Vnth (nat_to_fin (le_n_S (S o) n q)) (insert a0 (Nat.le_trans m (S o) n (le_S m o p) q) v) = Vnth (nat_to_fin q) v.
Proof.
  revert o q m p.
  induction v; intro o.
  - intro q.
    contradiction (Nat.nle_succ_0 o q).
  - destruct o; intros q m.
    + destruct m; intro p.
      * reflexivity.
      * contradiction (Nat.nle_succ_0 m p).
    + destruct m; intro p.
      * simpl.
        apply f_equal with (f := fun t => Vnth t v).
        apply nat_to_fin_proof_irrelevance.
      * simpl insert.
        change (nat_to_fin q) with (Succ (nat_to_fin (le_S_n (S o) n q))).
        simpl Vnth.
        apply eq_trans with (y := Vnth (nat_to_fin (le_S_n (S (S o)) (S n) (le_n_S (S (S o)) (S n) q))) (insert a0 (le_S_n m n (Nat.le_trans (S m) (S (S o)) (S n) (le_S (S m) (S o) p) q)) v)).
          reflexivity.
          rewrite nat_to_fin_proof_irrelevance with (p := le_S_n (S (S o)) (S n) (le_n_S (S (S o)) (S n) q)) (q := le_n_S (S o) n (le_S_n (S o) n q)).
          rewrite insert_proof_irrelevance with (p := le_S_n m n (Nat.le_trans (S m) (S (S o)) (S n) (le_S (S m) (S o) p) q)) (q := Nat.le_trans m (S o) n (le_S m o (le_S_n m o p)) (le_S_n (S o) n q)).
          apply IHv.
Qed.

Lemma insert_vnth_eq (A : Type) (n m : nat) (a0 : A) (p : m <= n) (v : vect A n) :
  Vnth (nat_to_fin (le_n_S m n p)) (insert a0 p v) = a0.
Proof.
  revert m p.
  induction v; intros m p.
  - destruct m.
    + reflexivity.
    + contradiction (Nat.nle_succ_0 m p).
  - destruct m.
    + reflexivity.
    + simpl insert.
      change (Vnth (nat_to_fin (le_n_S (S m) (S n) p)) (Vcons a (insert a0 (le_S_n m n p) v))) with (Vnth (nat_to_fin (le_S_n (S m) (S n) (le_n_S (S m) (S n) p))) (insert a0 (le_S_n m n p) v)).
      rewrite nat_to_fin_proof_irrelevance with (p := (le_S_n (S m) (S n) (le_n_S (S m) (S n) p))) (q := le_n_S m n (le_S_n m n p)).
      apply IHv.
Qed.


Lemma fin_incl_proof_irrelevance (n m : nat) (p q : m <= n) :
  fin_incl p = fin_incl q.
Proof.
  revert m p q.
  induction n; intro m.
  - destruct m; intros p q.
    + reflexivity.
    + contradiction (Nat.nle_succ_0 m p).
  - destruct m; intros p q.
    + reflexivity.
    + simpl fin_incl.
      rewrite IHn with (p := le_S_n m n p) (q := le_S_n m n q).
      reflexivity.
Qed.

Lemma vect_proj_proof_irrelevance (A : Type) (n m : nat) (p q : m <= n) :
  @vect_proj A n m p = @vect_proj A n m q.
Proof.
  revert m p q.
  induction n; intro m.
  - destruct m; intros p q.
    + reflexivity.
    + contradiction (Nat.nle_succ_0 m p).
  - destruct m; intros p q.
    + reflexivity.
    + simpl vect_proj.
      rewrite IHn with (p := le_S_n m n p) (q := le_S_n m n q).
      reflexivity.
Qed.

Lemma nat_to_fin_incl (n m o : nat) (p : m < n) (q : n <= o) :
  fin_incl q (nat_to_fin p) = nat_to_fin (Nat.le_trans (S m) n o p q).
Proof.
  revert n q m p.
  induction o.
  - intros n q m p.
    contradiction (Nat.nle_succ_0 m (Nat.le_trans (S m) n 0 p q)).
  - induction n; intro q.
    + intros m p.
      contradiction (Nat.nle_succ_0 m p).
    + induction m; intro p.
      * reflexivity.
      * simpl.
        apply f_equal with (f := @Succ o).
        rewrite nat_to_fin_proof_irrelevance with (p := le_S_n (S m) o (Nat.le_trans (S (S m)) (S n) (S o) p q)) (q := Nat.le_trans (S m) n o (le_S_n (S m) n p) (le_S_n n o q)).
        apply IHo with (q := le_S_n n o q) (p := le_S_n (S m) n p).
Qed.

(** Definition of formulas **)

Inductive form : Type :=
  | free_var (x : nat)
  | bound_var (x : nat) 
  | bot
  | imp (s t : form)
  | conj (s t : form)
  | disj (s t : form)
  | for_all (s : form)
  | exist (s : form).

(* Replacing a bound variable by a given free variable *)

Fixpoint unbind_rec (s : form) (x height : nat) : form :=
  match s with
    | free_var n => free_var n
    | bound_var n => remove_nat height bound_var 0 (free_var x) n
    | bot => bot
    | imp s t => imp (unbind_rec s x height) (unbind_rec t x height)
    | conj s t => conj (unbind_rec s x height) (unbind_rec t x height)
    | disj s t => disj (unbind_rec s x height) (unbind_rec t x height)
    | for_all s => for_all (unbind_rec s x (S height))
    | exist s => exist (unbind_rec s x (S height))
    end.

Definition unbind (s : form) (x : nat) : form :=
  unbind_rec s x 0.

(** Predicate which ensures that a given free variable does not appear in a formula **)

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

(** Predicate which ensures that all bound variables are linked to a quantifier **)

Inductive is_valid : nat -> form -> Prop :=
| Valid_free_var : forall (depth x : nat), is_valid depth (free_var x)
| Valid_bound_var : forall (depth n : nat), n < depth -> is_valid depth (bound_var n)
| Valid_bot : forall (depth : nat), is_valid depth bot
| Valid_imp : forall (depth : nat) (s t : form), is_valid depth s -> is_valid depth t -> is_valid depth (imp s t)
| Valid_conj : forall (depth : nat) (s t : form), is_valid depth s -> is_valid depth t -> is_valid depth (conj s t)
| Valid_disj : forall (depth : nat) (s t : form), is_valid depth s -> is_valid depth t -> is_valid depth (disj s t)
| Valid_for_all : forall (depth : nat) (s : form), is_valid (S depth) s -> is_valid depth (for_all s)
| Valid_exist : forall (depth : nat) (s : form), is_valid (S depth) s -> is_valid depth (exist s).

Lemma valid_bound_var_eq (depth n : nat) :
  is_valid depth (bound_var n) -> n < depth.
Proof.
  remember (bound_var n) as s.
  intro HValid.
  destruct HValid; solve [discriminate Heqs | injection Heqs; intro Eqs; rewrite <- Eqs; assumption].
Qed.

Lemma valid_imp_eq (depth : nat) (s t : form) :
  is_valid depth (imp s t) -> is_valid depth s /\ is_valid depth t.
Proof.
  remember (imp s t) as u.
  intro HValid.
  destruct HValid; solve [discriminate Hequ | injection Hequ; intros Eqt Eqs; rewrite <- Eqt; rewrite <- Eqs; split; assumption]. 
Qed.

Lemma valid_conj_eq (depth : nat) (s t : form) :
  is_valid depth (conj s t) -> is_valid depth s /\ is_valid depth t.
Proof.
  remember (conj s t) as u.
  intro HValid.
  destruct HValid; solve [discriminate Hequ | injection Hequ; intros Eqt Eqs; rewrite <- Eqt; rewrite <- Eqs; split; assumption]. 
Qed.

Lemma valid_disj_eq (depth : nat) (s t : form) :
  is_valid depth (disj s t) -> is_valid depth s /\ is_valid depth t.
Proof.
  remember (disj s t) as u.
  intro HValid.
  destruct HValid; solve [discriminate Hequ | injection Hequ; intros Eqt Eqs; rewrite <- Eqt; rewrite <- Eqs; split; assumption]. 
Qed.

Lemma valid_for_all_eq (depth : nat) (s : form) :
  is_valid depth (for_all s) -> is_valid (S depth) s.
Proof.
  remember (for_all s) as t.
  intro HValid.
  destruct HValid; solve [discriminate Heqt | injection Heqt; intro Eqs; rewrite <- Eqs; assumption].
Qed.

Lemma valid_exist_eq (depth : nat) (s : form) :
  is_valid depth (exist s) -> is_valid (S depth) s.
Proof.
  remember (exist s) as t.
  intro HValid.
  destruct HValid; solve [discriminate Heqt | injection Heqt; intro Eqs; rewrite <- Eqs; assumption].
Qed.

Lemma is_valid_increasing (f : form) (depth depth' : nat) :
  depth <= depth' -> is_valid depth f -> is_valid depth' f.
Proof.
  intros Hle Hvalid.
  revert depth' Hle.
  induction Hvalid; intros depth' Hle.
  - apply Valid_free_var.
  - apply Valid_bound_var.
    apply Nat.le_trans with (m := depth).
    + apply H.
    + apply Hle.
  - apply Valid_bot.
  - apply Valid_imp.
    + apply IHHvalid1.
      apply Hle.
    + apply IHHvalid2.
      apply Hle.
  - apply Valid_conj.
    + apply IHHvalid1.
      apply Hle.
    + apply IHHvalid2.
      apply Hle.
  - apply Valid_disj.
    + apply IHHvalid1.
      apply Hle.
    + apply IHHvalid2.
      apply Hle.
  - apply Valid_for_all.
    apply IHHvalid.
    apply le_n_S.
    apply Hle.
  - apply Valid_exist.
    apply IHHvalid.
    apply le_n_S.
    apply Hle.
Qed.

Lemma is_valid_eventually (f : form) :
  exists (depth : nat), is_valid depth f.
Proof.
  induction f.
  - exists 0.
    apply Valid_free_var.
  - exists (S x).
    apply Valid_bound_var.
    apply Nat.le_refl.
  - exists 0.
    apply Valid_bot.
  - destruct IHf1.
    destruct IHf2.
    exists (Nat.max x x0).
    apply Valid_imp.
    + apply (is_valid_increasing (Nat.le_max_l x x0) H).
    + apply (is_valid_increasing (Nat.le_max_r x x0) H0).
  - destruct IHf1.
    destruct IHf2.
    exists (Nat.max x x0).
    apply Valid_conj.
    + apply (is_valid_increasing (Nat.le_max_l x x0) H).
    + apply (is_valid_increasing (Nat.le_max_r x x0) H0).
  - destruct IHf1.
    destruct IHf2.
    exists (Nat.max x x0).
    apply Valid_disj.
    + apply (is_valid_increasing (Nat.le_max_l x x0) H).
    + apply (is_valid_increasing (Nat.le_max_r x x0) H0).
  - destruct IHf.
    exists x.
    apply Valid_for_all.
    apply (is_valid_increasing (Nat.le_succ_diag_r x) H).
  - destruct IHf.
    exists x.
    apply Valid_exist.
    apply (is_valid_increasing (Nat.le_succ_diag_r x) H).
Qed.

Lemma valid_unbind_rec (f : form) (x depth height : nat) :
  height <= depth -> (is_valid (S depth) f <-> is_valid depth (unbind_rec f x height)).
Proof.
  revert depth height.
  induction f; intros depth height Hle; unfold unbind_rec.
  - split; intro H; apply Valid_free_var.
  - destruct Nat.lt_trichotomy with (n := x0) (m := height).
    + rewrite remove_nat_lt.
        split; intro H0; apply Valid_bound_var.
        apply Nat.le_trans with (m := height).
          apply H.
          apply Hle.
        apply Nat.le_trans with (m := height).
          apply H.
          apply le_S.
          apply Hle.
        apply H.
    + destruct H.
      * rewrite H.
        rewrite remove_nat_eq.
        split; intro H0.
          apply Valid_free_var.
          apply Valid_bound_var.
          apply le_n_S.
          apply Hle.
      * destruct x0.
          contradiction (Nat.nle_succ_0 height H).
          rewrite remove_nat_gt.
            split; intro H0; apply Valid_bound_var.
              apply le_S_n.
              apply (valid_bound_var_eq H0).
              apply le_n_S.
              apply (valid_bound_var_eq H0).
              apply le_S_n.
            apply H.
  - split; intro H; apply Valid_bot.
  - split; intro H.
    + apply Valid_imp.
      * apply IHf1.
          apply Hle.
          apply (valid_imp_eq H).
      * apply IHf2.
          apply Hle.
          apply (valid_imp_eq H).
    + apply Valid_imp.
      * apply <- IHf1.
          apply (valid_imp_eq H).
          apply Hle.
      * apply <- IHf2.
          apply (valid_imp_eq H).
          apply Hle.
  - split; intro H.
    + apply Valid_conj.
      * apply IHf1.
          apply Hle.
          apply (valid_conj_eq H).
      * apply IHf2.
          apply Hle.
          apply (valid_conj_eq H).
    + apply Valid_conj.
      * apply <- IHf1.
          apply (valid_conj_eq H).
          apply Hle.
      * apply <- IHf2.
          apply (valid_conj_eq H).
          apply Hle.
  - split; intro H.
    + apply Valid_disj.
      * apply IHf1.
          apply Hle.
          apply (valid_disj_eq H).
      * apply IHf2.
          apply Hle.
          apply (valid_disj_eq H).
    + apply Valid_disj.
      * apply <- IHf1.
          apply (valid_disj_eq H).
          apply Hle.
      * apply <- IHf2.
          apply (valid_disj_eq H).
          apply Hle.
  - split; intro H.
    + apply Valid_for_all.
      apply IHf.
      * apply le_n_S.
        apply Hle.
      * apply (valid_for_all_eq H).
    + apply Valid_for_all.
      apply <- IHf.
      * apply (valid_for_all_eq H).
      * apply le_n_S.
        apply Hle.
  - split; intro H.
    + apply Valid_exist.
      apply IHf.
      * apply le_n_S.
        apply Hle.
      * apply (valid_exist_eq H).
    + apply Valid_exist.
      apply <- IHf.
      * apply (valid_exist_eq H).
      * apply le_n_S.
        apply Hle.
Qed.

Inductive is_valid_ctx : nat -> list form -> Prop :=
  | Valid_nil : forall (depth : nat), is_valid_ctx depth []
  | Valid_cons : forall (depth : nat) (a : form) (A : list form), is_valid depth a -> is_valid_ctx depth A -> is_valid_ctx depth (a::A).

Lemma valid_cons_eq (depth : nat) (a : form) (A : list form) :
  is_valid_ctx depth (a::A) -> is_valid depth a /\ is_valid_ctx depth A.
Proof.
  remember (a::A) as A'.
  intro HValid.
  destruct HValid.
  - discriminate HeqA'.
  - injection HeqA'.
    intros EqA Eqa.
    rewrite <- EqA.
    rewrite <- Eqa.
    split; assumption.
Qed.

Lemma is_valid_ctx_increasing (A : list form) (depth depth' : nat) :
  depth <= depth' -> is_valid_ctx depth A -> is_valid_ctx depth' A.
Proof.
  intros Hle HValid.
  induction HValid.
  - apply Valid_nil.
  - apply Valid_cons.
    + apply (is_valid_increasing Hle H).
    + apply (IHHValid Hle).
Qed.

(** Exchanging all the occurences of two given variables in a formula **)

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
  - simpl.
    generalize 0 as offset.
    revert x0.
    induction height; intro x0.
    + destruct x0; intro offset; reflexivity.
    + destruct x0; intro offset.
      * reflexivity.
      * apply IHheight.
  - reflexivity.
  - simpl exchange_vars.
    unfold unbind_rec.
    apply f_equal2.
    + apply IHs1.
    + apply IHs2.
  - simpl exchange_vars.
    unfold unbind_rec.
    apply f_equal2.
    + apply IHs1.
    + apply IHs2.
  - simpl exchange_vars.
    unfold unbind_rec.
    apply f_equal2.
    + apply IHs1.
    + apply IHs2.
  - simpl exchange_vars.
    unfold unbind_rec.
    apply f_equal.
    apply IHs.
  - simpl exchange_vars.
    unfold unbind_rec.
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

(** Exchanging the occurences of two given variables in a context **)

Definition exchange_vars_ctx (A : list form) (x y : nat) : list form :=
  map (fun (s : form) => exchange_vars s x y) A.

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

Print In.
Print incl.

Notation "s ~> t" := (imp s t) ( at level 51, right associativity).
Notation neg s := ( imp s bot).
Reserved Notation "A |- s" (at level 70).

(** 2.a : Defining proofs and proving weakness *)

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
      rewrite <- exchange_non_free_vars_ctx with (A := A) (x := x) (y := x0).
      * apply incl_map.
        assumption.
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
        rewrite <- exchange_non_free_vars_ctx with (A := A) (x := x) (y := x0).
          apply incl_map.
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

(** 2.b : Defining Heyting algebras and proving their base properties **)

Record HeytingAlgebra : Type :=
{ H : Type;
  leq : H -> H -> Prop;
  leq_refl s : leq s s;
  leq_trans s t u: (leq s t -> leq t u -> leq s u);
  bottom : H;
  inf : (H -> Prop) -> H;
  impl : H -> H -> H;
  leq_bottom u : leq bottom u;
  leq_inf (P : H -> Prop) u : (forall (s:H), P s -> leq u s) <-> leq u (inf P);
  leq_impl s t u : (leq (inf (finite_set [s;t])) u) <-> leq s (impl t u)
}.

Definition meet {HA} (s t : H HA) : H HA := inf (finite_set [s;t]).

Lemma leq_meet {HA} (s t u : H HA) :
  (leq u s /\ leq u t) <-> leq u (meet s t).
Proof.
  unfold meet.
  rewrite <- leq_inf.
  split; intro H.
  - destruct H.
    intros s0 H2.
    destruct H2.
    destruct H2.
    + rewrite <- H2. assumption.
    + destruct H2.
      * rewrite <- H2. assumption.
      * contradiction (in_nil H2).
  - split; apply H; apply Finite_set.
    + apply in_eq.
    + apply in_cons.
      apply in_eq.
Qed.

Definition sup {HA} (P : H HA -> Prop) : H HA :=
  inf (fun_image (fun (t : H HA) => impl (inf (fun_image (fun (s : H HA) => impl s t) P)) t) (fun _ => True)).

Lemma leq_sup {HA} (P : H HA -> Prop) u :
  (forall (s : H HA), P s -> leq s u) <-> leq (sup P) u.
Proof.
  split; intro H0.
  - apply leq_trans with (t := impl (inf (fun_image (fun (s : H HA) => impl s u) P)) u).
    + unfold sup.
      apply leq_inf with (P := fun_image (fun (t : H HA) => impl (h:=HA) (inf (h:=HA) (fun_image (fun (s : H HA) => impl (h:=HA) s t) P)) t)
        (fun _ : H HA => True)) (u := (inf (fun_image (fun t : H HA => impl (h:=HA) (inf (fun_image (fun (s : H HA) => impl (h:=HA) s t) P)) t)
        (fun _ : H HA => True)))).
      * apply leq_refl.
      * apply Fun_image with (f := fun (t : H HA) => impl (inf (fun_image (fun (s : H HA) => impl s t) P)) t) (a := u).
        trivial.
    + apply leq_trans with (t := impl (impl (bottom HA) (bottom HA)) u).
      * apply leq_impl.
        apply leq_trans with (t := meet (impl (h:=HA) (inf (h:=HA) (fun_image (fun s : H HA => impl (h:=HA) s u) P)) u) (inf (h:=HA) (fun_image (fun s : H HA => impl (h:=HA) s u) P))).
          apply leq_meet. split.
            apply leq_meet with (s := impl (inf (fun_image (fun (s : H HA) => impl s u) P)) u) (t := impl (bottom HA) (bottom HA)) (u := meet (impl (inf (fun_image (fun (s : H HA) => impl s u) P)) u) (impl (bottom HA) (bottom HA))).
              apply leq_refl.
            apply leq_trans with (t := impl (bottom HA) (bottom HA)).
              apply leq_meet with (s := impl (inf (fun_image (fun (s : H HA) => impl s u) P)) u) (t := impl (bottom HA) (bottom HA)) (u := meet (impl (inf (fun_image (fun (s : H HA) => impl s u) P)) u) (impl (bottom HA) (bottom HA))).
                apply leq_refl.
              apply leq_inf.
              intros s H1.
              destruct H1.
              apply leq_impl.
              apply leq_trans with (t := a).
                apply leq_meet with (s := impl (bottom HA) (bottom HA)) (t := a) (u := meet (impl (bottom HA) (bottom HA)) a).
                apply leq_refl.
                apply (H0 a H1).
              apply leq_impl.
              apply leq_refl.
      * apply leq_trans with (t := meet (impl (impl (bottom HA) (bottom HA)) u) (impl (bottom HA) (bottom HA))).
          apply leq_meet. split.
            apply leq_refl.
            apply leq_impl.
            apply leq_trans with (t := bottom HA).
              apply leq_meet with (s := impl (impl (bottom HA) (bottom HA)) u) (t := bottom HA) (u := meet (impl (impl (bottom HA) (bottom HA)) u) (bottom HA)).
              apply leq_refl.
              apply leq_refl.
            apply leq_impl.
            apply leq_refl.
  - intros s H1.
    apply leq_trans with (t := sup P).
    + unfold sup.
      apply leq_inf.
      intros t H2.
      destruct H2.
      apply leq_impl.
      apply leq_trans with (t := meet (impl s a) s).
      * apply leq_meet. split.
          apply leq_trans with (t := inf (fun_image (fun (t : H HA) => impl t a) P)).
            apply leq_meet with (s := s) (t := inf (fun_image (fun (t : H HA) => impl t a) P)) (u := meet s (inf (fun_image (fun (t : H HA) => impl t a) P))).
            apply leq_refl.
            apply leq_inf with (P := fun_image (fun (t : H HA) => impl t a) P) (u := inf (fun_image (fun (t : H HA) => impl t a) P)).
              apply leq_refl.
              apply Fun_image with (f := fun (t : H HA) => impl t a) (a := s).
              apply H1.
          apply leq_meet with (s := s) (t := inf (fun_image (fun (t : H HA) => impl t a) P)) (u := meet s (inf (fun_image (fun (t : H HA) => impl t a) P))).
          apply leq_refl.
      * apply leq_impl.
        apply leq_refl.
    + apply H0.
Qed.

Definition join {HA} (s t : H HA) : H HA := sup (finite_set [s;t]).

Lemma leq_join {HA} (s t u : H HA) :
  ((leq s u) /\ (leq t u)) <-> leq (join s t) u.
Proof.
  unfold join.
  rewrite <- leq_sup.
  split; intro H.
  - destruct H.
    intros s0 H2.
    destruct H2.
    destruct H2.
    + rewrite <- H2. assumption.
    + destruct H2.
      * rewrite <- H2. assumption.
      * contradiction (in_nil H2).
  - split; apply H; apply Finite_set.
    + apply in_eq.
    + apply in_cons.
      apply in_eq.
Qed.

Lemma leq_impl_join {HA} (s t u : H HA) :
  leq (join s t) (impl (meet (impl s u) (impl t u)) u).
Proof.
  unfold join.
  unfold sup.
  apply leq_trans with (t := impl (inf (fun_image (fun (s0 : H HA) => impl s0 u) (finite_set [s;t]))) u).
  - apply leq_inf with (P := fun_image (fun t0 : H HA => impl (h:=HA) (inf (h:=HA) (fun_image (fun s0 : H HA => impl (h:=HA) s0 t0) (finite_set [s; t]))) t0) (fun _ : H HA => True)).
    + apply leq_refl.
    + apply Fun_image with (f := fun (t0 : H HA) => impl (inf (fun_image (fun (s0 : H HA) => impl s0 t0) (finite_set [s;t]))) t0) (a := u).
      trivial.
  - apply leq_impl.
    apply leq_trans with (t := meet (impl (inf (fun_image (fun (s0 : H HA) => impl s0 u) (finite_set [s;t]))) u) (inf (fun_image (fun (s0 : H HA) => impl s0 u) (finite_set [s;t])))). 
    + apply leq_meet.
      split.
      * apply leq_meet with (t := meet (impl s u) (impl t u)).
        apply leq_refl.
      * apply leq_trans with (t := meet (impl s u) (impl t u)).
          apply leq_meet with (s := impl (inf (fun_image (fun (s0 : H HA) => impl s0 u) (finite_set [s; t]))) u).
          apply leq_refl.
          apply leq_inf.
          intros s0 H0.
          do 3 (destruct H0).
            rewrite <- H0.
            apply leq_meet with (t := impl t u).
            apply leq_refl.
            destruct H0.
              rewrite <- H0.
              apply leq_meet with (s := impl s u).
              apply leq_refl.
              contradiction (in_nil H0).
    + apply leq_impl.
      apply leq_refl.
Qed.

(** 2.c : Defining evaluation of a formula *)

Fixpoint eval_rec {HA} (val : nat -> H HA) (f : form) (depth : nat) : is_valid depth f -> vect (H HA) depth -> H HA :=
  match f with
  | free_var x => fun _ => fun _ => val x
  | bound_var n => fun p => Vnth (nat_to_fin (valid_bound_var_eq p))
  | bot => fun _ => fun _ => bottom HA
  | imp s t => fun p => fun v => impl (eval_rec val (proj1 (valid_imp_eq p)) v) (eval_rec val (proj2 (valid_imp_eq p)) v)
  | conj s t => fun p => fun v => meet (eval_rec val (proj1 (valid_conj_eq p)) v) (eval_rec val (proj2 (valid_conj_eq p)) v)
  | disj s t => fun p => fun v => join (eval_rec val (proj1 (valid_disj_eq p)) v) (eval_rec val (proj2 (valid_disj_eq p)) v)
  | for_all s => fun p => fun v => inf (fun_image (fun x => eval_rec val (valid_for_all_eq p) (Vcons x v)) (fun _ => True))
  | exist s => fun p => fun v => sup (fun_image (fun x => eval_rec val (valid_exist_eq p) (Vcons x v)) (fun _ => True))
  end.

Lemma eval_rec_proof_irrelevance {HA} (val : nat -> H HA) (f : form) (depth : nat) (p q : is_valid depth f) :
  eval_rec val p = eval_rec val q.
Proof.
  revert depth p q.
  induction f; intros depth p q.
  - reflexivity.
  - simpl eval_rec.
    apply f_equal with (f := fun t v => Vnth t v).
    apply nat_to_fin_proof_irrelevance.
  - reflexivity.
  - simpl eval_rec.
    apply f_equal2 with (f := fun f1 f2 v => impl (f1 v) (f2 v)).
    + apply IHf1.
    + apply IHf2.
  - simpl eval_rec.
    apply f_equal2 with (f := fun f1 f2 v => meet (f1 v) (f2 v)).
    + apply IHf1.
    + apply IHf2.
  - simpl eval_rec.
    apply f_equal2 with (f := fun f1 f2 v => join (f1 v) (f2 v)).
    + apply IHf1.
    + apply IHf2.
  - simpl eval_rec.
    apply f_equal with (f := fun f v => inf (fun_image (fun x => f (Vcons x v)) (fun _ => True))).
    apply IHf.
  - simpl eval_rec.
    apply f_equal with (f := fun f v => sup (fun_image (fun x => f (Vcons x v)) (fun _ => True))).
    apply IHf.
Qed.

(* We define the equivalence relation of equivalence so that we can une antisymmetry in Heyting algebras *)

Definition equivalent {HA} (u v : H HA) : Prop := leq u v /\ leq v u.

Lemma equivalent_meet {HA} (s s' t t' : H HA) :
  equivalent s s' -> equivalent t t' -> equivalent (meet s t) (meet s' t').
Proof.
  intros Hs Ht.
  split.
  - apply leq_meet.
    split.
    + apply leq_trans with (t := s).
      * apply leq_meet with (s := s) (t := t) (u := meet s t).
        apply leq_refl.
      * apply Hs.
    + apply leq_trans with (t := t).
      * apply leq_meet with (s := s) (t := t) (u := meet s t).
        apply leq_refl.
      * apply Ht.
  - apply leq_meet.
    split.
    + apply leq_trans with (t := s').
      * apply leq_meet with (s := s') (t := t') (u := meet s' t').
        apply leq_refl.
      * apply Hs.
    + apply leq_trans with (t := t').
      * apply leq_meet with (s := s') (t := t') (u := meet s' t').
        apply leq_refl.
      * apply Ht.
Qed.

Lemma equivalent_join {HA} (s s' t t' : H HA) :
  equivalent s s' -> equivalent t t' -> equivalent (join s t) (join s' t').
Proof.
  intros Hs Ht.
  split.
  - apply leq_join.
    split.
    + apply leq_trans with (t := s').
      * apply Hs.
      * apply leq_join with (s := s') (t := t') (u := join s' t').
        apply leq_refl.
    + apply leq_trans with (t := t').
      * apply Ht.
      * apply leq_join with (s := s') (t := t') (u := join s' t').
        apply leq_refl.
  - apply leq_join.
    split.
    + apply leq_trans with (t := s).
      * apply Hs.
      * apply leq_join with (s := s) (t := t) (u := join s t).
        apply leq_refl.
    + apply leq_trans with (t := t).
      * apply Ht.
      * apply leq_join with (s := s) (t := t) (u := join s t).
        apply leq_refl.
Qed.

Lemma equivalent_impl {HA} (s s' t t' : H HA) :
  equivalent s s' -> equivalent t t' -> equivalent (impl s t) (impl s' t').
Proof.
  intros Hs Ht.
  split.
  - apply leq_impl.
    apply leq_trans with (t := meet (impl s t) s).
    + apply equivalent_meet.
      * split; apply leq_refl.
      * apply Hs.
    + apply leq_trans with (t := t).
      * apply leq_impl.
        apply leq_refl.
      * apply Ht.
  - apply leq_impl.
    apply leq_trans with (t := meet (impl s' t') s').
    + apply equivalent_meet.
      * split; apply leq_refl.
      * split; apply Hs.
    + apply leq_trans with (t := t').
      * apply leq_impl.
        apply leq_refl.
      * apply Ht.
Qed.

Lemma equivalent_inf {HA} (f g : H HA -> H HA) (P : H HA -> Prop) :
  (forall (s : H HA), P s -> equivalent (f s) (g s)) -> equivalent (inf (fun_image f P)) (inf (fun_image g P)).
Proof.
  intro Hs.
  split.
  - apply leq_inf.
    intros s Hg.
    destruct Hg.
    apply leq_trans with (t := f a).
    + apply leq_inf with (P := fun_image f P).
      * apply leq_refl.
      * apply Fun_image.
        apply H0.
    + apply Hs.
      apply H0.
  - apply leq_inf.
    intros s Hg.
    destruct Hg.
    apply leq_trans with (t := g a).
    + apply leq_inf with (P := fun_image g P).
      * apply leq_refl.
      * apply Fun_image.
        apply H0.
    + apply Hs.
      apply H0.
Qed.

Lemma equivalent_sup {HA} (f g : H HA -> H HA) (P : H HA -> Prop) :
  (forall (s : H HA), P s -> equivalent (f s) (g s)) -> equivalent (sup (fun_image f P)) (sup (fun_image g P)).
Proof.
  intro Hs.
  split.
  - apply leq_sup.
    intros s Hg.
    destruct Hg.
    apply leq_trans with (t := g a).
    + apply Hs.
      apply H0.
    + apply leq_sup with (P := fun_image g P).
      * apply leq_refl.
      * apply Fun_image.
        apply H0.
  - apply leq_sup.
    intros s Hg.
    destruct Hg.
    apply leq_trans with (t := f a).
    + apply Hs.
      apply H0.
    + apply leq_sup with (P := fun_image f P).
      * apply leq_refl.
      * apply Fun_image.
        apply H0.
Qed.

Lemma eval_rec_vect_proj {HA} (val : nat -> H HA) (f : form) (depth depth' : nat) (p : depth <= depth') (q : is_valid depth f) (v : vect (H HA) depth') :
  equivalent (eval_rec val (is_valid_increasing p q) v) (eval_rec val q (vect_proj p v)).
Proof.
  revert depth depth' p q v.
  induction f; intros depth depth' p q v; simpl eval_rec.
  - split; apply leq_refl.
  - rewrite nat_to_fin_proof_irrelevance with (p := valid_bound_var_eq (is_valid_increasing p q)) (q := Nat.le_trans (S x) depth depth' (valid_bound_var_eq q) p).
    rewrite <- nat_to_fin_incl with (p := valid_bound_var_eq q) (q := p).
    rewrite vect_proj_vnth with (p := p) (t := nat_to_fin (valid_bound_var_eq q)) (v := v).
    split; apply leq_refl.
  - split; apply leq_refl.
  - apply equivalent_impl.
    + rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_imp_eq (is_valid_increasing p q))) (q := is_valid_increasing p (proj1 (valid_imp_eq q))).
      apply IHf1 with (p := p) (q := proj1 (valid_imp_eq q)).
    + rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_imp_eq (is_valid_increasing p q))) (q := is_valid_increasing p (proj2 (valid_imp_eq q))).
      apply IHf2 with (p := p) (q := proj2 (valid_imp_eq q)).
  - apply equivalent_meet.
    + rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_conj_eq (is_valid_increasing p q))) (q := is_valid_increasing p (proj1 (valid_conj_eq q))).
      apply IHf1 with (p := p) (q := proj1 (valid_conj_eq q)).
    + rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_conj_eq (is_valid_increasing p q))) (q := is_valid_increasing p (proj2 (valid_conj_eq q))).
      apply IHf2 with (p := p) (q := proj2 (valid_conj_eq q)).
  - apply equivalent_join.
    + rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_disj_eq (is_valid_increasing p q))) (q := is_valid_increasing p (proj1 (valid_disj_eq q))).
      apply IHf1 with (p := p) (q := proj1 (valid_disj_eq q)).
    + rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_disj_eq (is_valid_increasing p q))) (q := is_valid_increasing p (proj2 (valid_disj_eq q))).
      apply IHf2 with (p := p) (q := proj2 (valid_disj_eq q)).
  - apply equivalent_inf.
    intros s _.
    rewrite eval_rec_proof_irrelevance with (p := valid_for_all_eq (is_valid_increasing p q)) (q := is_valid_increasing (le_n_S depth depth' p) (valid_for_all_eq q)).
    rewrite vect_proj_proof_irrelevance with (p := p) (q := le_S_n depth depth' (le_n_S depth depth' p)).
    change (Vcons s (vect_proj (le_S_n depth depth' (le_n_S depth depth' p)) v)) with (vect_proj (le_n_S depth depth' p) (Vcons s v)).
    apply IHf with (p := le_n_S depth depth' p) (q := valid_for_all_eq q).
  - apply equivalent_sup.
    intros s _.
    rewrite eval_rec_proof_irrelevance with (p := valid_exist_eq (is_valid_increasing p q)) (q := is_valid_increasing (le_n_S depth depth' p) (valid_exist_eq q)).
    rewrite vect_proj_proof_irrelevance with (p := p) (q := le_S_n depth depth' (le_n_S depth depth' p)).
    change (Vcons s (vect_proj (le_S_n depth depth' (le_n_S depth depth' p)) v)) with (vect_proj (le_n_S depth depth' p) (Vcons s v)).
    apply IHf with (p := le_n_S depth depth' p) (q := valid_exist_eq q).
Qed.

(** 2.d We define the equivalent of the function Meet_list **)

Fixpoint Meet_valid_ctx {HA} (val : nat -> H HA) (A : list form) (depth : nat) : is_valid_ctx depth A -> vect (H HA) depth -> H HA :=
  match A with
  | [] => fun p v => impl (bottom HA) (bottom HA)
  | a::A => fun p v => meet (eval_rec val (proj1 (valid_cons_eq p)) v) (Meet_valid_ctx val (proj2 (valid_cons_eq p)) v)
  end.

Lemma Meet_valid_ctx_proof_irrelevance HA (val : nat -> H HA) A depth (p q : is_valid_ctx depth A) :
  Meet_valid_ctx val p = Meet_valid_ctx val q.
Proof.
  revert p q.
  induction A; intros p q.
  - reflexivity.
  - simpl Meet_valid_ctx.
    apply f_equal2 with (f := fun f1 f2 v => meet (f1 v) (f2 v)).
    + apply eval_rec_proof_irrelevance.
    + apply IHA.
Qed.

Lemma Meet_valid_ctx_vect_proj HA (val : nat -> H HA) (A : list form) (depth depth' : nat) (p : depth <= depth') (q : is_valid_ctx depth A) (v : vect (H HA) depth') :
  equivalent (Meet_valid_ctx val (is_valid_ctx_increasing p q) v) (Meet_valid_ctx val q (vect_proj p v)).
Proof.
  revert q.
  induction A; intro q.
  - split; apply leq_refl.
  - simpl Meet_valid_ctx.
    apply equivalent_meet.
    + rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_cons_eq (is_valid_ctx_increasing p q))) (q := is_valid_increasing p (proj1 (valid_cons_eq q))).
      apply eval_rec_vect_proj.
    + rewrite Meet_valid_ctx_proof_irrelevance with (p := proj2 (valid_cons_eq (is_valid_ctx_increasing p q))) (q := is_valid_ctx_increasing p (proj2 (valid_cons_eq q))).
      apply IHA.
Qed.

Lemma eval_rec_change_val HA (val : nat -> H HA) (f : form) (depth : nat) (p : is_valid depth f) (x : nat) (u : H HA) :
  not_free_in x f -> eval_rec val p = eval_rec (change_val val x u) p.
Proof.
  intro NF.
  revert depth p.
  induction NF; intros depth p.
  - simpl.
    unfold change_val.
    rewrite ((proj2 (Nat.eqb_neq m n)) H0).
    reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite <- IHNF1.
    rewrite <- IHNF2.
    reflexivity.
  - simpl.
    rewrite <- IHNF1.
    rewrite <- IHNF2.
    reflexivity.
  - simpl.
    rewrite <- IHNF1.
    rewrite <- IHNF2.
    reflexivity.
  - simpl.
    rewrite IHNF.
    reflexivity.
  - simpl.
    rewrite IHNF.
    reflexivity.
Qed.

Lemma Meet_valid_ctx_change_val HA (val : nat -> H HA) (A : list form) (depth : nat) (p : is_valid_ctx depth A) (x : nat) (u : H HA) :
  not_free_in_ctx x A -> Meet_valid_ctx val p = Meet_valid_ctx (change_val val x u) p.
Proof.
  intro H.
  induction H.
  - reflexivity.
  - simpl.
    rewrite <- eval_rec_change_val.
    rewrite <- IHnot_free_in_ctx.
    reflexivity.
    apply H0.
Qed.

Lemma eval_rec_unbind HA (val : nat -> H HA) (f : form) (depth : nat) (p : is_valid (S depth) f) (v : vect (H HA) depth) (x : nat) :
  equivalent (eval_rec val (proj1 (valid_unbind_rec f x (Nat.le_0_l depth)) p) v) (eval_rec val p (Vcons (val x) v)).
Proof.
  rewrite (f_equal (eval_rec val p) (match v as v0 in (vect _ n0) return (Vcons (val x) v0 = insert (val x) (Nat.le_0_l n0) v0) with
                                                       | Vnil _ => eq_refl
                                                       | @Vcons _ n0 a v0 => eq_refl
                                                       end)).
  generalize (Nat.le_0_l depth) as q.
  generalize 0 as height.
  revert depth p v.
  induction f; intros depth p v height q.
  - split; apply leq_refl.
  - generalize (proj1 (valid_unbind_rec (bound_var x0) x q) p) as r.
    destruct Nat.lt_trichotomy with (n := x0) (m := height); simpl unbind_rec.
    + simpl unbind_rec.
      rewrite remove_nat_lt with (x := height) (f := bound_var) (default := free_var x) (y := x0).
      * intro r.
        simpl eval_rec.
        rewrite nat_to_fin_proof_irrelevance with (p := valid_bound_var_eq r) (q := Nat.le_trans (S x0) height depth H0 q).
        change (match x0 as m0 return (m0 < S depth -> fin (S depth)) with
                | 0 => fun _ : 0 < S depth => Zero depth
                | S m => fun p0 : S m < S depth => Succ (nat_to_fin (n:=depth) (m:=m) (le_S_n (S m) depth p0))
                end (valid_bound_var_eq p)) with (nat_to_fin (valid_bound_var_eq p)).
        rewrite nat_to_fin_proof_irrelevance with (p := valid_bound_var_eq p) (q := le_S (S x0) depth (Nat.le_trans (S x0) height depth H0 q)).
        rewrite insert_vnth_lt.
        split; apply leq_refl.
      * apply H0.
    + destruct H0.
      * revert p.
        rewrite H0.
        rewrite remove_nat_eq.
        intros p r.
        simpl eval_rec.
        change (match height as m0 return (m0 < S depth -> fin (S depth)) with
                | 0 => fun _ : 0 < S depth => Zero depth
                | S m => fun p0 : S m < S depth => Succ (nat_to_fin (n:=depth) (m:=m) (le_S_n (S m) depth p0))
                end (valid_bound_var_eq p)) with (nat_to_fin (valid_bound_var_eq p)).
        rewrite nat_to_fin_proof_irrelevance with (p := valid_bound_var_eq p) (q := le_n_S height depth q).
        rewrite insert_vnth_eq.
        split; apply leq_refl.
      * destruct x0. contradiction (Nat.nle_succ_0 height H0).
        rewrite remove_nat_gt with (x := height) (f := bound_var) (default := free_var x) (y := x0).
          intro r.
          change (eval_rec val p (insert (val x) q v)) with (Vnth (nat_to_fin (valid_bound_var_eq p)) (insert (val x) q v)).
          simpl eval_rec.
          rewrite nat_to_fin_proof_irrelevance with (p := valid_bound_var_eq p) (q := le_n_S (S x0) depth (valid_bound_var_eq r)).
          rewrite insert_proof_irrelevance with (p := q) (q := Nat.le_trans height (S x0) depth (le_S height x0 (le_S_n height x0 H0)) (valid_bound_var_eq r)).
          rewrite insert_vnth_gt.
          split; apply leq_refl.
          apply le_S_n.
          apply H0.
  - split; apply leq_refl.
  - simpl.
    apply equivalent_impl.
    + rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_imp_eq (proj1 (valid_unbind_rec (imp f1 f2) x q) p))) (q := proj1 (valid_unbind_rec f1 x q) (proj1 (valid_imp_eq p))).
      apply IHf1.
    + rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_imp_eq (proj1 (valid_unbind_rec (imp f1 f2) x q) p))) (q := proj1 (valid_unbind_rec f2 x q) (proj2 (valid_imp_eq p))).
      apply IHf2.
  - simpl.
    apply equivalent_meet.
    + rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_conj_eq (proj1 (valid_unbind_rec (conj f1 f2) x q) p))) (q := proj1 (valid_unbind_rec f1 x q) (proj1 (valid_conj_eq p))).
      apply IHf1.
    + rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_conj_eq (proj1 (valid_unbind_rec (conj f1 f2) x q) p))) (q := proj1 (valid_unbind_rec f2 x q) (proj2 (valid_conj_eq p))).
      apply IHf2.
  - simpl.
    apply equivalent_join.
    + rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_disj_eq (proj1 (valid_unbind_rec (disj f1 f2) x q) p))) (q := proj1 (valid_unbind_rec f1 x q) (proj1 (valid_disj_eq p))).
      apply IHf1.
    + rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_disj_eq (proj1 (valid_unbind_rec (disj f1 f2) x q) p))) (q := proj1 (valid_unbind_rec f2 x q) (proj2 (valid_disj_eq p))).
      apply IHf2.
  - simpl.
    apply equivalent_inf.
    intros s _.
    rewrite insert_proof_irrelevance with (p := q) (q := le_S_n height depth (le_n_S height depth q)).
    change (Vcons s (insert (val x) q v)) with (insert (val x) (le_n_S height depth q) (Vcons s v)).
    rewrite eval_rec_proof_irrelevance with (p := valid_for_all_eq (proj1 (valid_unbind_rec (for_all f) x q) p)) (q := proj1 (valid_unbind_rec f x (le_n_S height depth q)) (valid_for_all_eq p)).
    apply IHf.
  - simpl.
    apply equivalent_sup.
    intros s _.
    rewrite insert_proof_irrelevance with (p := q) (q := le_S_n height depth (le_n_S height depth q)).
    change (Vcons s (insert (val x) q v)) with (insert (val x) (le_n_S height depth q) (Vcons s v)).
    rewrite eval_rec_proof_irrelevance with (p := valid_exist_eq (proj1 (valid_unbind_rec (exist f) x q) p)) (q := proj1 (valid_unbind_rec f x (le_n_S height depth q)) (valid_exist_eq p)).
    apply IHf.
Qed.

(** 2.e Proving soundness of Heyting semantics **)

Lemma nd_soundHA_rec HA (val : nat -> H HA) (A : list form) (s : form) (depth : nat) (p : is_valid_ctx depth A) (q : is_valid depth s) (v : vect (H HA) depth) :
  nd A s -> leq (Meet_valid_ctx val p v) (eval_rec val q v).
Proof.
  intro ND.
  revert val depth p q v.
  induction ND; intros val depth p q v.
  - induction A.
    + contradiction (in_nil H0).
    + destruct H0; simpl Meet_valid_ctx.
      * clear IHA.
        revert q. rewrite <- H0. intro q.
        rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_cons_eq p)) (q := q).
        apply leq_meet with (s := eval_rec val q v) (t := Meet_valid_ctx val (proj2 (valid_cons_eq p)) v) (u := meet (eval_rec val q v) (Meet_valid_ctx val (proj2 (valid_cons_eq p)) v)).
        apply leq_refl.
      * apply leq_trans with (t := Meet_valid_ctx val (proj2 (valid_cons_eq p)) v).
          apply leq_meet with (s := eval_rec val (proj1 (valid_cons_eq p)) v) (t := Meet_valid_ctx val (proj2 (valid_cons_eq p)) v) (u := meet (eval_rec val (proj1 (valid_cons_eq p)) v) (Meet_valid_ctx val (proj2 (valid_cons_eq p)) v)).
          apply leq_refl.
          apply IHA.
          apply H0.
  - apply leq_trans with (t := bottom HA).
    + apply IHND with (p := p) (q := Valid_bot depth).
    + apply leq_bottom.
  - simpl eval_rec. 
    apply leq_impl.
    apply leq_trans with (t := Meet_valid_ctx val (Valid_cons (proj1 (valid_imp_eq q)) p) v).
    + simpl Meet_valid_ctx.
      rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_cons_eq (Valid_cons (proj1 (valid_imp_eq q)) p))) (q := proj1 (valid_imp_eq q)).
      rewrite Meet_valid_ctx_proof_irrelevance with (p := proj2 (valid_cons_eq (Valid_cons (proj1 (valid_imp_eq q)) p))) (q := p).
      apply leq_meet.
      split;
        apply leq_meet with (s := Meet_valid_ctx val p v) (t := eval_rec val (proj1 (valid_imp_eq q)) v) (u := meet (Meet_valid_ctx val p v) (eval_rec val (proj1 (valid_imp_eq q)) v));
        apply leq_refl.
    + apply IHND.
  - destruct (is_valid_eventually s) as (depth',r).
    apply leq_trans with (t :=  Meet_valid_ctx val p (vect_proj (Nat.le_max_l depth depth') (vect_app (bottom HA) (Nat.le_max_l depth depth') v))).
      rewrite vect_proj_app_inv.
      apply leq_refl.
    apply leq_trans with (t := Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
      apply Meet_valid_ctx_vect_proj.
    apply leq_trans with (t := eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
    + apply leq_trans with (t := meet (eval_rec val (Valid_imp (is_valid_increasing (Nat.le_max_r depth depth') r) (is_valid_increasing (Nat.le_max_l depth depth') q)) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)) (eval_rec val (is_valid_increasing (Nat.le_max_r depth depth') r) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))).
      * apply leq_meet.
        split.
          apply IHND2.
          apply IHND1.
      * apply leq_impl.
        simpl eval_rec.
        rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_imp_eq (Valid_imp (is_valid_increasing (Nat.le_max_r depth depth') r) (is_valid_increasing (Nat.le_max_l depth depth') q)))) (q := is_valid_increasing (Nat.le_max_r depth depth') r).
        rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_imp_eq (Valid_imp (is_valid_increasing (Nat.le_max_r depth depth') r) (is_valid_increasing (Nat.le_max_l depth depth') q)))) (q := is_valid_increasing (Nat.le_max_l depth depth') q).
        apply leq_refl.
    + apply leq_trans with (t := eval_rec val q (vect_proj (Nat.le_max_l depth depth') (vect_app (bottom HA) (Nat.le_max_l depth depth') v))).
      * apply eval_rec_vect_proj.
      * rewrite vect_proj_app_inv.
        apply leq_refl.
  - simpl eval_rec.
    apply leq_meet.
    split.
    + apply IHND1.
    + apply IHND2.
  - destruct (is_valid_eventually s) as (depth',r).
    rewrite <- vect_proj_app_inv with (a0 := bottom HA) (p := Nat.le_max_l depth depth') (v := v).
    apply leq_trans with (t :=  Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
      + apply Meet_valid_ctx_vect_proj.
      + apply leq_trans with (t := eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
        * apply leq_meet with (s := eval_rec val (is_valid_increasing (Nat.le_max_r depth depth') r) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)) (t := eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
          rewrite eval_rec_proof_irrelevance with (p := is_valid_increasing (Nat.le_max_r depth depth') r) (q := proj1 (valid_conj_eq (Valid_conj (is_valid_increasing (Nat.le_max_r depth depth') r) (is_valid_increasing (Nat.le_max_l depth depth') q)))).
          rewrite eval_rec_proof_irrelevance with (p := is_valid_increasing (Nat.le_max_l depth depth') q) (q := proj2 (valid_conj_eq (Valid_conj (is_valid_increasing (Nat.le_max_r depth depth') r) (is_valid_increasing (Nat.le_max_l depth depth') q)))).
          apply IHND.
        * apply eval_rec_vect_proj.
  - destruct (is_valid_eventually t) as (depth',r).
    rewrite <- vect_proj_app_inv with (a0 := bottom HA) (p := Nat.le_max_l depth depth') (v := v).
    apply leq_trans with (t :=  Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
      + apply Meet_valid_ctx_vect_proj.
      + apply leq_trans with (t := eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
        * apply leq_meet with (t := eval_rec val (is_valid_increasing (Nat.le_max_r depth depth') r) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)) (s := eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
          rewrite eval_rec_proof_irrelevance with (p := is_valid_increasing (Nat.le_max_r depth depth') r) (q := proj2 (valid_conj_eq (Valid_conj (is_valid_increasing (Nat.le_max_l depth depth') q) (is_valid_increasing (Nat.le_max_r depth depth') r)))).
          rewrite eval_rec_proof_irrelevance with (p := is_valid_increasing (Nat.le_max_l depth depth') q) (q := proj1 (valid_conj_eq (Valid_conj (is_valid_increasing (Nat.le_max_l depth depth') q) (is_valid_increasing (Nat.le_max_r depth depth') r)))).
          apply IHND.
        * apply eval_rec_vect_proj.
  - apply leq_trans with (t := eval_rec val (proj2 (valid_disj_eq q)) v).
    + apply IHND.
    + simpl eval_rec.
      apply leq_join with (s := eval_rec val (proj1 (valid_disj_eq q)) v).
      apply leq_refl.
  - apply leq_trans with (t := eval_rec val (proj1 (valid_disj_eq q)) v).
    + apply IHND.
    + simpl eval_rec.
      apply leq_join with (t := eval_rec val (proj2 (valid_disj_eq q)) v).
      apply leq_refl.
  - destruct (is_valid_eventually (disj s t)) as (depth',r).
    rewrite <- vect_proj_app_inv with (a0 := bottom HA) (p := Nat.le_max_l depth depth') (v := v).
    apply leq_trans with (t :=  Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
      + apply Meet_valid_ctx_vect_proj.
      + apply leq_trans with (t := eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
        * apply leq_trans with (t := meet
                                      (impl 
                                        (meet 
                                          (impl
                                             (eval_rec val (proj1 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                             (eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                          )
                                          (impl
                                             (eval_rec val (proj2 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                             (eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                          )
                                        )
                                        (eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                      )
                                      (meet
                                        (impl
                                          (eval_rec val (proj1 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                          (eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                        )
                                        (impl
                                           (eval_rec val (proj2 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                           (eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                        )
                                      )
                            ).
            apply leq_meet.
            split.
              apply leq_trans with (t := eval_rec val (is_valid_increasing (Nat.le_max_r depth depth') r) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
                apply IHND1.
                apply leq_impl_join.
              apply leq_meet.
              split.
                rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (q := proj1 (valid_imp_eq (Valid_imp (proj1 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (is_valid_increasing (Nat.le_max_l depth depth') q)))).
                rewrite eval_rec_proof_irrelevance with (p := is_valid_increasing (Nat.le_max_l depth depth') q) (q := proj2 (valid_imp_eq (Valid_imp (proj1 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (is_valid_increasing (Nat.le_max_l depth depth') q)))).
                apply IHND2.
                rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (q := proj1 (valid_imp_eq (Valid_imp (proj2 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (is_valid_increasing (Nat.le_max_l depth depth') q)))).
                rewrite eval_rec_proof_irrelevance with (p := is_valid_increasing (Nat.le_max_l depth depth') q) (q := proj2 (valid_imp_eq (Valid_imp (proj2 (valid_disj_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (is_valid_increasing (Nat.le_max_l depth depth') q)))).
                apply IHND3.
            apply leq_impl.
            apply leq_refl.
        * apply eval_rec_vect_proj.
  - simpl eval_rec.
    apply leq_inf.
    intros s0 H2.
    destruct H2.
    rewrite <- change_val_refl with (f := val) (x := x) (a := a).
    rewrite eval_rec_change_val with (x := x) (u := a).
    rewrite Meet_valid_ctx_change_val with (x := x) (u := a).
    apply leq_trans with (t := eval_rec (change_val val x a) (proj1 (valid_unbind_rec s x (Nat.le_0_l depth)) (valid_for_all_eq q)) v).
    + apply IHND.
    + apply eval_rec_unbind.
    + apply H0.
    + apply H1.
  - apply leq_trans with (t := eval_rec val (Valid_for_all (proj2 (valid_unbind_rec s x (Nat.le_0_l depth)) q)) v).
    + apply IHND.
    + apply leq_trans with (t := eval_rec val (proj2 (valid_unbind_rec s x (Nat.le_0_l depth)) q) (Vcons (val x) v)).
      * apply leq_inf with (P := fun_image (fun (u : H HA) => eval_rec val (proj2 (valid_unbind_rec s x (Nat.le_0_l depth)) q) (Vcons u v)) (fun _ => True)).
          rewrite eval_rec_proof_irrelevance with (p := proj2 (valid_unbind_rec s x (Nat.le_0_l depth)) q) (q := valid_for_all_eq (Valid_for_all (proj2 (valid_unbind_rec s x (Nat.le_0_l depth)) q))).
          apply leq_refl.
          apply Fun_image with (a := val x).
          trivial.
      * rewrite eval_rec_proof_irrelevance with (p := q) (q := (proj1 (valid_unbind_rec s x (Nat.le_0_l depth)) (proj2 (valid_unbind_rec s x (Nat.le_0_l depth)) q))).
        apply eval_rec_unbind.
  - apply leq_trans with (t := eval_rec val (proj1 (valid_unbind_rec s x (Nat.le_0_l depth)) (valid_exist_eq q)) v).
    + apply IHND.
    + apply leq_trans with (t := eval_rec val (valid_exist_eq q) (Vcons (val x) v)).
      * apply eval_rec_unbind.
      * apply leq_sup with (P := fun_image (fun (u : H HA) => eval_rec val (valid_exist_eq q) (Vcons u v)) (fun _ => True)).
          apply leq_refl.
          apply Fun_image with (a := val x).
          trivial.
  - destruct (is_valid_eventually (exist s)) as (depth',r).
    rewrite <- vect_proj_app_inv with (a0 := bottom HA) (p := Nat.le_max_l depth depth') (v := v).
    apply leq_trans with (t :=  Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
      + apply Meet_valid_ctx_vect_proj.
      + apply leq_trans with (t := eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
        * apply leq_trans with (t := meet
                                      (eval_rec val (is_valid_increasing (Nat.le_max_r depth depth') r) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                                      (Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))
                               ).
            apply leq_meet.
            split.
              apply IHND1.
              apply leq_refl.
            apply leq_impl.
            apply (proj1 (leq_sup (fun_image (fun x0 : H HA => eval_rec val (valid_exist_eq (is_valid_increasing (Nat.le_max_r depth depth') r)) (Vcons x0 (vect_app (bottom HA) (Nat.le_max_l depth depth') v))) (fun _ : H HA => True)) (impl (h:=HA) (Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)) (eval_rec val (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))))).
            intros s0 H.
            destruct H.
            apply leq_impl.
            apply leq_trans with (t := meet (Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)) (eval_rec val (valid_exist_eq (is_valid_increasing (Nat.le_max_r depth depth') r)) (Vcons a (vect_app (bottom HA) (Nat.le_max_l depth depth') v)))).
              apply leq_meet.
              split.
                apply leq_meet with (s := eval_rec val (valid_exist_eq (is_valid_increasing (Nat.le_max_r depth depth') r)) (Vcons a (vect_app (bottom HA) (Nat.le_max_l depth depth') v))).
                apply leq_refl.
                apply leq_meet with (t := Meet_valid_ctx val (is_valid_ctx_increasing (Nat.le_max_l depth depth') p) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)).
                apply leq_refl.
              apply leq_impl.
              rewrite <- change_val_refl with (f := val) (x := x) (a := a).
              rewrite Meet_valid_ctx_change_val with (val := val) (x := x) (u := a).
              rewrite eval_rec_change_val with (val := val) (x := x) (u := a).
              rewrite eval_rec_change_val with (val := val) (x := x) (u := a).
              apply leq_trans with (t := impl (h:=HA) (eval_rec (change_val val x a) (proj1 (valid_unbind_rec s x (Nat.le_0_l (Nat.max depth depth'))) (valid_exist_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (vect_app (bottom HA) (Nat.le_max_l depth depth') v)) (eval_rec (change_val val x a) (is_valid_increasing (Nat.le_max_l depth depth') q) (vect_app (bottom HA) (Nat.le_max_l depth depth') v))).
                rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_unbind_rec s x (Nat.le_0_l (Nat.max depth depth')))
           (valid_exist_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (q := proj1 (valid_imp_eq (Valid_imp (proj1 (valid_unbind_rec s x (Nat.le_0_l (Nat.max depth depth')))
           (valid_exist_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (is_valid_increasing (Nat.le_max_l depth depth') q)))).
                rewrite eval_rec_proof_irrelevance with (p := is_valid_increasing (Nat.le_max_l depth depth') q) (q := proj2 (valid_imp_eq (Valid_imp (proj1 (valid_unbind_rec s x (Nat.le_0_l (Nat.max depth depth')))
           (valid_exist_eq (is_valid_increasing (Nat.le_max_r depth depth') r))) (is_valid_increasing (Nat.le_max_l depth depth') q)))).
                apply IHND2.
                apply equivalent_impl.
                  split; apply eval_rec_unbind.
                  split; apply leq_refl.
              apply H2.
              apply H1.
              apply H0.
      * apply eval_rec_vect_proj.
Qed.

(** We now harmonize the notations to match the normal version of this exercise **)

Record valid_form : Type :=
{
  f : form;
  proof : is_valid 0 f
}.

Definition eval {HA} (val : nat -> H HA) (s : valid_form) : H HA :=
  eval_rec val (proof s) (Vnil (H HA)).

Fixpoint valid_ctx_from_list (A : list valid_form) : is_valid_ctx 0 (map f A) :=
  match A with
  | [] => Valid_nil 0
  | s::A => Valid_cons (proof s) (valid_ctx_from_list A)
  end.

Fixpoint Meet_list {HA} (val : nat -> H HA) (A : list valid_form) : H HA :=
  match A with
  | [] => impl (bottom HA) (bottom HA)
  | s::A => meet (eval val s) (Meet_list val A)
  end.

Lemma Meet_list_equivalence {HA} (val : nat -> H HA) (A : list valid_form) :
  Meet_list val A = Meet_valid_ctx val (valid_ctx_from_list A) (Vnil (H HA)).
Proof.
  induction A.
  - reflexivity.
  - simpl.
    apply f_equal2.
    + rewrite eval_rec_proof_irrelevance with (p := proj1 (valid_cons_eq (Valid_cons (proof a) (valid_ctx_from_list A)))) (q := proof a).
      reflexivity.
    + rewrite Meet_valid_ctx_proof_irrelevance with (p := proj2 (valid_cons_eq (Valid_cons (proof a) (valid_ctx_from_list A)))) (q := valid_ctx_from_list A).
      apply IHA.
Qed.

Definition hent {HA} (val : nat -> H HA) (A : list valid_form) (s : valid_form) := leq (Meet_list val A) (eval val s).

Lemma nd_soundHA {HA} (val : nat -> H HA) (A : list valid_form) (s : valid_form) :
  nd (map f A) (f s) -> hent val A s.
Proof.
  intro ND.
  unfold hent.
  rewrite Meet_list_equivalence.
  unfold eval.
  apply nd_soundHA_rec.
  apply ND.
Qed.









