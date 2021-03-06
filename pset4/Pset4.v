Require Import Frap Pset4Sig.
Require Import OrdersFacts.

(* Before beginning this problem set, please see Pset4Sig.v,
 * which contains the instructions.
 *)

(* For your convenience, we beforehand provide some useful facts about orders.
 * You can skim through the list of theorems by using "Print," or visiting 
 * this page:
 * https://coq.inria.fr/library/Coq.Structures.OrdersFacts.html
 *)
Include (OrderedTypeFacts Pset4Sig).
Include (OrderedTypeTest Pset4Sig).
(* Print OrderedTypeFacts. *)
(* Print OrderedTypeTest. *)

(* Our solution only needs (at most) the following facts from the above libraries.
 * But it is certainly okay if you use facts beyond these! 
 *)
Check eq_lt.
Check eq_sym.
Check lt_eq.
Check lt_not_eq.
Check lt_trans.
Check compare_refl.
Check compare_lt_iff. (* Note that this one can be used with [apply], despite the fact that it
                       * includes an "if and only if" ([<->]) where other theorems use simple
                       * implication ([->]). *)
Check compare_gt_iff.
Check compare_eq_iff.

Print BST.
Print tree.
Check tree_ind.
Check t.
Check member.
Print member.

Theorem insert_member: forall t n, BST t -> member n (insert n t) = true.
Proof.
  induction t.
  - simpl.
    intros.
    Check compare_refl.
    rewrite compare_refl.
    reflexivity.
  - Check lt_not_eq.
    Search (lt _ _).
    simpl.
    Check compare.
    Print comparison.
    Print comparison_ind.
    intros.
    remember (compare n d).
    destruct c; simpl; rewrite <- Heqc.
    +
      reflexivity.
    +
      apply IHt1.
      apply H.
    +
      apply IHt2.
      apply H.
Qed.


Lemma foo: forall t n d, tree_lt d t -> lt n d -> tree_lt d (insert n t).
Proof.
  intros.
  induction t.
  - compute.
    firstorder.
  - simpl.
    (* remember (compare n d0).  *)
    destruct (compare n d0); repeat (split + apply H + apply IHt1 + apply IHt2).
Qed.

Lemma foo2: forall t n d, tree_gt d t -> lt d n -> tree_gt d (insert n t).
Proof.
  intros.
  induction t.
  - compute.
    firstorder.
  - simpl.
    (* remember (compare n d0).  *)
    destruct (compare n d0); repeat (split + apply H + apply IHt1 + apply IHt2).
Qed.

Theorem insert_ok: forall t n, BST t -> BST (insert n t).
Proof.
  induction t.
  - compute.
    (* unfold insert. *)
    (* simpl. *)
    (* unfold tree_lt. *)
    (* simpl. *)
    (* unfold tree_gt. *)
    (* simpl. *)
    intros.
    repeat split; trivial.
  -
    intros.
    simpl.
    remember (compare n d).
    destruct c.
    * apply H.
    * simpl.
      split.
    + apply IHt1.
      destruct H as [H1 [H2 [H3 H4]]].
      apply H1.
    +
      split.
      apply foo.
      apply H.
      Print Lt.
      Print lt.
      Check compare_lt_iff.
      apply compare_lt_iff.
      Search (?x = ?y -> ?y = ?x).
      symmetry.
      apply Heqc; repeat (split || apply H).
      split; repeat (apply H || apply foo2).
      * split; repeat (split || apply H || apply foo2).
        ++ apply IHt2.
           apply H.
        ++ apply compare_gt_iff.
           symmetry.
           assumption.
Qed.


    (* remember H. *)
    (* destruct H as [BST_t1 [ ltd [BST_t2 gtd]]]. *)
    (* induction c. *)
    (* + simpl. *)
    (*   assumption. *)
    (* + simpl. *)
    (*   repeat split. *)
    (*   * apply (IHt1 n BST_t1). *)

Theorem delete_ok: forall t n, BST t -> BST (delete n t).
Proof.
Admitted.

(* OPTIONAL PART! *)
(*Theorem delete_member: forall t n, BST t -> member n (delete n t) = false.
Proof.
Admitted.*)
