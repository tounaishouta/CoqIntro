Require Import ssreflect.

Section Propositional.

  Variable A B C : Prop.

  Section Disjunction.

    Locate "\/".

    Check or.

    Print or.

    Check or_introl.
    Check or_intror.
    Check or_ind.

    Lemma or_trans : (A \/ B) \/ C -> A \/ (B \/ C).
    Proof.
      apply or_ind. (* case. *)
      apply or_ind. (* case. *)
      move => a.
      apply or_introl. (* left. *)
      apply a.
      move => b.
      apply or_intror. (* right. *)
      apply or_introl. (* left. *)
      apply b.
      move => c.
      apply or_intror. (* right. *)
      apply or_intror. (* right. *)
      apply c.
    Qed.

    Lemma or_trans' : A \/ (B \/ C) -> (A \/ B) \/ C.
    Proof.
      case.
      move => a.
      left.
      left.
      apply a.
      case.
      move => b.
      left.
      right.
      apply b.
      apply or_intror.
    Qed.

    Lemma or_comm : A \/ B -> B \/ A.
    Proof.
      case.
      apply or_intror.
      apply or_introl.
    Qed.

    Lemma or_iden : A \/ A -> A.
    Proof.
      case.
      move => a.
      apply a.
      move => a.
      apply a.
    Qed.

  End Disjunction.

  Section Conjunction.

    Locate "/\".

    Check and.

    Print and.

    Check conj.
    Check and_ind.

    Lemma and_eliml : A /\ B -> A.
    Proof.
      case.
      move => a b.
      apply a.
    Qed.

    Lemma and_comm : A /\ B -> B /\ A.
    Proof.
      case.
      move => a b.
      apply conj. (* split. *)
      apply b.
      apply a.
    Qed.

    Lemma and_elimr : A /\ B -> B.
    Proof.
      case.
      move => a b.
      apply b.
    Qed.

    Lemma and_trans : (A /\ B) /\ C -> A /\ (B /\ C).
    Proof.
      case.
      case.
      move => a b c.
      split.
      apply a.
      split.
      apply b.
      apply c.
    Qed.

    Lemma and_trans' : A /\ (B /\ C) -> (A /\ B) /\ C.
    Proof.
      case.
      move => a.
      case.
      move => b c.
      split.
      split.
      apply a.
      apply b.
      apply c.
    Qed.

    Lemma and_iden : A -> A /\ A.
    Proof.
      move => a.
      split.
      apply a.
      apply a.
    Qed.

  End Conjunction.

  Section Negation.

    Locate "~".
    Check not.
    Print not.

    Check False.
    Print False.
    Check False_ind.

    Lemma disj_syll : A \/ B -> ~ A -> B.
    Proof.
      unfold "~".
      case.
      move => a not_a.
      apply False_ind. (* exfalso. *)
      apply not_a.
      apply a.
      move => b not_a.
      apply b.
    Qed.

    Lemma double_neg_intro : A -> ~ ~ A.
    Proof.
      unfold "~".
      move => a not_a.
      apply not_a.
      apply a.
    Qed.

    Hypothesis double_neg_elim : forall P : Prop, ~ ~ P -> P.

    Lemma excluded_middle : A \/ ~ A.
    Proof.
      apply double_neg_elim.
      unfold "~".
      move => H.
      apply H.
      right.
      move => a.
      apply H.
      left.
      apply a.
    Qed.

    Lemma triple_neg : ~ ~ ~ A -> ~ A.
    Proof.
      (* unfold "~". *)
      move => not_not_not_a a.
      apply not_not_not_a.
      apply double_neg_intro.
      apply a.
    Qed.

    Lemma de_morgan_1 : ~ (A \/ B) -> (~ A /\ ~ B).
    Proof.
      move => H.
      split.
      move => a.
      apply H.
      left.
      apply a.
      move => b.
      apply H.
      right.
      apply b.
    Qed.

    Lemma de_morgan_1' : (~ A /\ ~ B) -> ~ (A \/ B).
    Proof.
      (* unfold "~". *)
      case.
      move => not_a not_b.
      case.
      apply not_a.
      apply not_b.
    Qed.

    Lemma de_morgan_2 : ~ (A /\ B) -> (~ A \/ ~ B).
    Proof.
      move => H1.
      apply double_neg_elim.
      move => H2.
      apply H2.
      left.
      move => a.
      apply H2.
      right.
      move => b.
      apply H1.
      split.
      apply a.
      apply b.
    Qed.

    Lemma de_morgan_2' : (~ A \/ ~ B) -> ~ (A /\ B).
    Proof.
      case.
      move => not_a.
      case.
      move => a b.
      apply not_a.
      apply a.
      move => not_b.
      case.
      move => a b.
      apply not_b.
      apply b.
    Qed.

    Lemma de_morgan_3 : (A -> B) -> (~ B -> ~ A).
    Proof.
      move => H not_b a.
      apply not_b.
      apply H.
      apply a.
    Qed.

    Lemma de_morgan_3' : (~ B -> ~ A) -> (A -> B).
    Proof.
      move => H a.
      apply double_neg_elim.
      move => not_b.
      apply H.
      apply not_b.
      apply a.
    Qed.

  End Negation.

End Propositional.
