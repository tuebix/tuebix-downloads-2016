(* ******************** *)
(* Aussagenlogik in Coq *)
(* ******************** *)

(* Transitivität der Implikation *)

Theorem imp_trans: forall P Q R: Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
 intros P Q R.
 intros H0 H1.
 intro.
 apply H1.
 apply H0.
 assumption.
 Show Proof.
Qed.

(* Distributivität von "oder" "\/" und "und" "/\" *)

Theorem or_distrib: forall P Q R: Prop, (P /\ Q) \/ R -> (P \/ R) /\ (Q \/ R).
Proof. 
 intros P Q R.
 intro H.
 destruct H as [ HPQ | HR ].
  split.
   Check proj1.
   left. apply proj1 with (B:=Q). assumption.
   left. apply proj2 with (A:=P). assumption.
  split.
   right. assumption.
   right. assumption.
 Show Proof.
Qed.

(* nochmal, jetzt mit automatischem Beweis *)

Theorem or_distrib': forall P Q R: Prop, (P /\ Q) \/ R -> (P \/ R) /\ (Q \/ R).
Proof.
 tauto.
 Show Proof.
Qed.

(* *************** *)
(* Abhängige Typen *)
(* *************** *)

(* algebraischer Datentyp, strikte Version von C union *)
Inductive A : Set :=
 | ANat :  nat -> A
 | ABool : bool -> A
.

(* Funktion, die den Typ der Instanz liefert *)
Fixpoint atype (a : A) : Type :=
 match a with
  | ANat n  => nat
  | ABool b => bool
end.

Example atype_nat: atype (ANat 1) = nat.
Proof.
  simpl. reflexivity.
Qed.

Example atype_bool: atype (ABool true) = bool.
Proof.
 simpl. reflexivity. 
Qed.

(* Funktion, die "inneren" Wert liefert, strikt! *)
Fixpoint aval (a : A) : (atype a) :=
 match a with
 | ANat n  => n
 | ABool b => b
end.

Example aval_nat: aval (ANat 1) = 1.
Proof.
  reflexivity. 
Qed.

Example aval_nat_all: forall n:nat, aval (ANat n) = n.
Proof. 
  intro. simpl. reflexivity.
Qed.

Example aval_bool: aval (ABool true) = true.
Proof.
  reflexivity.
Qed.

Definition nat_fun: nat -> nat.
 intro n.
 exact (n*n+4).
Show Proof.
Defined.

Check nat_fun. (* Typ zeigen *)
Print nat_fun. (* Definition zeigen *)

Definition all_self_equal: forall n:nat, n=n.
Proof. auto. Defined.

Print all_self_equal.
Check (fun n:nat => eq_refl).

(* ******************* *)
(* einfache Arithmetik *)
(* ******************* *)

Require Mult.

Lemma big_less: 1 < 6000.
Proof. 
 auto with arith.
 Show Proof.
Qed.

Lemma times2: forall n: nat, n+n=2*n.
Proof.
 intro n.
 induction n.
  reflexivity.
  Search (S _ + _).
  rewrite plus_Sn_m.
  Search (_ + _ = _ + _).
  rewrite PeanoNat.Nat.add_comm.
  rewrite plus_Sn_m.
  rewrite IHn.
  Search ( (_*S _) =_).
  rewrite PeanoNat.Nat.mul_succ_r.
  rewrite PeanoNat.Nat.add_comm.
  simpl.
  reflexivity.
Qed.

Theorem binom1: forall a b: nat, (a+b)*(a+b) = a*a + 2*a*b +b*b.
Proof.
 intros.
 Search ( (_+_)*_).
 rewrite PeanoNat.Nat.mul_add_distr_r.
 rewrite PeanoNat.Nat.mul_add_distr_l.
 rewrite PeanoNat.Nat.mul_add_distr_l.
 Search ( _*_ = _*_).
 rewrite PeanoNat.Nat.mul_comm with (n:=b).
 Search ( _ + (_+_) ).
 rewrite <- Plus.plus_assoc_reverse.
 Search (_+_ = _).
 rewrite PeanoNat.Nat.add_cancel_r with (p:=b*b).
 rewrite <- times2.
 rewrite PeanoNat.Nat.mul_add_distr_r.
 rewrite <- Plus.plus_assoc_reverse.
 reflexivity.
 Show Proof.
Qed.

Require Import Ring.
Require Import ArithRing.

Theorem binom1': forall a b: nat, (a+b)*(a+b) = a*a + 2*a*b +b*b.
Proof.
 intros.
 ring.
 Show Proof.
Qed.


(* ********************* *)
(* Beweisbares Sortieren *)
(* ********************* *)

Require Import List.

Inductive sorted : list nat -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall n:nat, sorted (n :: nil)
  | sorted2 : forall (n1 n2:nat) (l: list nat), n1 <= n2 -> 
              sorted (n2 :: l ) -> sorted (n1 :: n2 :: l).

Example sorted_123: sorted (1::2::3::nil).
Proof.
 apply sorted2. apply le_S. apply le_n.
 apply sorted2. auto with arith.
 apply sorted1.
Qed.

Example not_sorted_321: ~sorted (3::2::1::nil).
Proof.
 red. intro H. inversion H. subst. auto with arith.
 apply Gt.le_not_gt in H2. auto with arith.
Qed.

Hint Resolve sorted0 sorted1 sorted2 : sort.

Search({ _ <= _}+{ _ > _}).

Fixpoint insert (n: nat) (l: list nat) : list nat :=
 match l with
 | nil => n::nil
 | h::r => match (Compare_dec.le_gt_dec n h) with
           | left _ => n::h::r
           | right _ => h::(insert n r)
           end
end.

Notation "n ->> l" := (insert n l) (at level 60).

Lemma insert_sorted: forall (n: nat) (l: list nat),
                      sorted l -> sorted (insert n l).
Proof.
 intros n l H.
 elim H.
  simpl; auto with sort arith. 
  intro n0. simpl.
   case (Compare_dec.le_gt_dec n n0). intros; auto with sort arith.
   intros. apply sorted2. auto with arith. apply sorted1.
  intros n1 n2. simpl. 
   case (Compare_dec.le_gt_dec n n2). intros; auto with sort arith.
   case (Compare_dec.le_gt_dec n n1). intros; auto with sort arith.
    intros. auto with sort arith.
  intros. 
   case (Compare_dec.le_gt_dec n n1). intros; auto with sort arith.
   intros. apply sorted2; assumption.
Qed.


Fixpoint isort (l: list nat) : list nat :=
 match l with
 | nil => nil
 | h::r => insert h (isort r)
 end.

Eval compute in (isort (4::1::5::3::2::nil)).

Theorem isort_sorted: forall (l: list nat), sorted (isort l).
Proof.
 intro l.
 induction l.
  auto with sort.
  simpl.
  apply insert_sorted.
  assumption.
  Show Proof.
Qed.

