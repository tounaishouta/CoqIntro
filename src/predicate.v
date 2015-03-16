Require Import ssreflect.

Section Predicate.

  Section Quantifier.

    Variable A : Type.
    Variable B : Prop.
    Variable P Q : A -> Prop.

    Check forall x : A, P x.
    Check forall x : A, B.
    Check A -> B.

    Lemma HilbertS' : (forall x : A, P x -> Q x) -> (forall x : A, P x) -> forall x : A, Q x.
    Proof.
      move => g f x.
      apply g.
      apply f.
    Qed.

    Print HilbertS'.

    Lemma HilbertS'' : (forall x : A, P x -> B) -> (forall x : A, P x) -> A -> B.
    Proof.
      move => g f x.
      (* apply g. ===> Error *)
      apply g with x.
      apply f.
    Qed.

    Print HilbertS''.

    Locate "exists".
    Check exists x : A, P x.
    Check ex P.
    Check ex.
    Print ex.
    Check ex_intro.
    Check ex_ind.

    Lemma forall_exists : (forall x : A, P x -> Q x) -> (exists x : A, P x) -> (exists y : A, Q y).
    Proof.
      move => g.
      case.
      move => x px.
      apply ex_intro with x. (* exists x. *)
      apply g.
      apply px.
    Qed.

  End Quantifier.

  Section Peano.

    Print nat.

  End Peano.

End Predicate.
