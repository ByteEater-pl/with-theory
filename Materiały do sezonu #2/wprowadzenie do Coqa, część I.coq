(* 1.1 Writing correct formulas *)
Check True.
Check False.
Check 3.
Check (3+4).
Check (3=5).
Check (3,4).
Check ((3=5)/\True).
Check nat -> Prop.
Check (3 <= 6).
Check (3,3=5):nat*Prop.
Check (fun x:nat => x = 3).
Check nat.
Check Type.
Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).
Check (let f := fun x => (x * 3,x) in f 3).
Locate "_ <= _".
Locate "_ * _".
Check True.
Check False.
Check and.
Check (and True False).
(* a -> b -> c means a -> (b -> c) *)
(* f a b means (f a) b *)

(* 1.2 Evaluating expressions *)
Compute let f := fun x => (x * 3, x) in f 3.

(* Exercise on functions *)
Definition add5(x1 x2 x3 x4 x5: nat) := x1+x2+x3+x4+x5.
Check add5.
Compute add5 5 7 2 09 00.

Compute if true then 3 else 5.

SearchPattern bool.

Definition is_zero (n:nat) :=
  match n with
    0 => true
  | S p => false
  end.

Print pred.
Print Nat.pred. (* Print Init.Nat.pred. *)

(*
Fixpoint rec_bad n :=
  match n with 0 => 0 | S p => rec_bad (S p) end.
*)
Fixpoint sum_n2 n s :=
  match n with
    0 => s
  | S p => sum_n2 p (p + s)
  end.
Fixpoint evenb n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
  end.

Require Import List.
Check 1::2::3::nil.
Compute map (fun x => x + 3) (1::3::2::nil).
Compute map S (1::22::3::nil).
Compute let l := (1::2::3::nil) in l ++ map (fun x => x + 3) l.

SearchPattern (nat -> nat -> bool).
Search Nat.eqb.

Require Import Arith.
Locate "_ =? _".

Fixpoint insert n l :=
  match l with
    nil => n::nil
  | a::tl => if n <=? a then n::l else a::insert n tl
  end.
Fixpoint sort l :=
  match l with
    nil => nil
  | a::tl => insert a (sort tl)
  end.
Compute sort (1::4::3::22::5::16::7::nil).

(* Exercise on lists, map, and app *)
(* my solution *)
Fixpoint lput[T: Set](a: T)(l: list T) :=
  match l with
  | nil => a::nil
  | h::t => h :: lput a t
  end.
Fixpoint iota(n: nat) :=
  match n with
  | S k => lput k (iota k)
  | 0 => nil
  end.
Compute iota 6.
(* Yves Bertot's solution *)
  Fixpoint first_n_aux (n:nat)(m:nat) :=
    match n with 0 => nil | S p => m :: first_n_aux p (m+1) end.

  Definition first_n (n:nat) := first_n_aux n 0.

(* Exercise on sorting *)
Definition sorted2(l: list nat) :=
  match l with
  | a::b::_ => a <=? b
  | _ => true
  end.
Fixpoint sorted(l: list nat) :=
  match l with
  | nil => true
  | _ :: t => andb (sorted2 l) (sorted t)
  end.
Compute sorted (0::0::4::5::8::nil).
Compute sorted (2::1::nil).

(* Exercise on counting *)
Fixpoint count_list(n: nat)(l: list nat) :=
  match l with
  | h::t => count_list n t + if h =? n then 1 else 0
  | _ => 0
  end.
Compute count_list 7 (0::9::7::7::3::0::11::7::13::nil).

Search True.
Print I.
Print True.
Print False.

SearchPattern (_ <= _).
Search (_ <= _) (_ + _).
SearchPattern (_ + _ <= _ + _).
SearchRewrite (_ + (_ - _)).

Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.
Proof.
intros a b H.
split.
destruct H as [H1 H2].
exact H2.
intuition.
Qed.

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
intros A B H.
destruct H as [H1 | H1].
right; assumption.
left; assumption.
Qed.

Check le_n.
Check le_S.
Lemma example4 : 3 <= 5.
Proof.
apply le_S.
apply le_S.
apply le_n.
Qed.

(* Exercise on logical connectives *)
(* my solution *)
Lemma conj_assoc: forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
intros.
destruct H.
destruct H0.
split.
split.
assumption.
assumption.
assumption.
Qed.
Lemma impl_compat_conj: forall A B C D: Prop,(A->B)/\(C->D)/\A/\C -> B/\D.
intros.
destruct H.
destruct H0.
destruct H1.
split.
apply H.
assumption.
apply H0.
assumption.
Qed.
Lemma law_of_contradiction: forall A: Prop, ~(A/\~A).
intro.
intro.
destruct H.
exact (H0 H).
Qed.
Lemma alt_assoc: forall A B C: Prop, A\/(B\/C)->(A\/B)\/C.
intros.
case H.
intro.
left.
left.
assumption.
intro.
case H0.
intro.
left.
right.
assumption.
right.
assumption.
Qed.
Lemma boolean: forall A B: Prop, (A\/B)/\~A -> B.
intros.
destruct H.
case H.
intro.
contradiction (H0 H1).
exact (fun x => x).
Qed.
(* parts of Yves Bertot's solution *)
Lemma lc2 : forall A B C D : Prop, (A->B)/\(C->D)/\A/\C->B/\D.
Proof.
intros A B C D h'; destruct h' as [f [g [ha hc]]]; split.
apply f; exact ha. apply g; exact hc.
Qed.
Lemma lc4 : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
intros A B C H. destruct H as [H | [H1 | H2]].
left; left; exact H.
left; right; exact H1.
right; exact H2.
Qed.
Lemma lc5 : forall A B : Prop, (A\/B)/\~A -> B.
Proof.
intros A B h'; destruct h' as [[ha | hb] na].
destruct na; exact ha.
exact hb.
Qed.
