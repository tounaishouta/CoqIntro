% 述語論理

このページでは述語論理の証明について見て行きましょう。

[説明に用いるスクリプトや演習の解答例](src/predicate.v)

全称量化子 `forall`
-------------------

[動かしてみる](tutorial.html) のページで型付きラムダ計算の公理２つ

* 関数適用

    `a : A` かつ `f : A -> B` ならば `f a : B` が成り立つ。

* 関数抽象

    仮定 `x : A` のもと `y : B` ならば、
    仮定 `x : A` なしに `fun x : A => y : A -> B` が成り立つ。
    但し、一般に `y` は `x` に依存する。

を紹介しましたが、実は不十分で次のように拡張されます。

* 関数適用

    `a : A` かつ `f : forall x : A, P x` ならば `f a : P a` が成り立つ。

* 関数抽象

    仮定 `x : A` のもと `y : P x` ならば、
    仮定 `x : A` なしに `fun x : A => y : forall x : A, P x` が成り立つ。
    但し、一般に `y` は `x` に依存する。

これは関数の出力の型が関数の入力に依存する場合を考えていて集合論の直積に対応します。
比較してみましょう。

* $a \in A$ かつ $(y _ x) _ {x \in A} \in \prod _ {x \in A} P _ x$ ならば
  $y _ a \in P _ a$ が成り立つ。

* $x \in A$ に対し $y _ x \in P _ x$ ならば
  $(y _ x) _ {x \in A} \in \prod _ {x \in A} P _ x$ が成り立つ。

基本の関数型 `A -> B` は出力の型が入力に依存しない特別な場合とみなすことができます。
実際、

    Require Import ssreflect.

    Section Predicate.

      Section Quantifier.

        Variable A : Type.
        Variable B : Prop.
        Variable P Q : A -> Prop.

        Check forall x : A, P x.
        Check forall x : A, B.
        Check A -> B.

を実行してみると、
`A -> B` と `forall x : A, B` は同様に扱われているのが分かります。

証明においても `move` を同様に用いることができます。
`apply` に関しては埋めるべき入力の穴を出力の型から推論して
自動で埋めてくれることがあります。
例を見てみましょう。

    Lemma HilbertS' : (forall x : A, P x -> Q x) -> (forall x : A, P x) -> forall x : A, Q x.
    Proof.
      move => g f x.
      apply g.
      apply f.
    Qed.

    Print HilbertS'.

`Print` した結果

    HilbertS' =
    fun (g : forall x : A, P x -> Q x) (f : forall x : A, P x) (x : A) =>
    g x (f x)
         : (forall x : A, P x -> Q x) -> (forall x : A, P x) -> forall x : A, Q x

をみると、
式は [動かしてみる](tutorial.html) で示した `HilbertS` に類似していることがわかります。
証明が短く済んでいるのは、subgoal の形から推論して `apply x.` を補ってくれているからです。

推論できない場合は `with` で補う必要があります。

    Lemma HilbertS'' : (forall x : A, P x -> B) -> (forall x : A, P x) -> A -> B.
    Proof.
      move => g f x.
      (* apply g. ===> Error *)
      apply g with x.
      apply f.
    Qed.

    Print HilbertS''.

`apply g.` をする際、subgoal `B` からでは、`x` を補うことができないので
`with x` を付け加える必要があります。
`Print` の結果を見ると `HilbertS''` も型を除いて `HilbertS` や `HilbertS'` と
同じ式であることがわかります。

存在量化子 `exists`
-------------------

存在量化子は先ほど見た `forall` を用いて定義されています。
実際に見てみましょう。

    Locate "exists".
    Check ex P.
    Check ex.
    Print ex.
    Check ex_intro.
    Check ex_ind.

実行結果から

* `exists x : A, P x` は `ex P` の書き換え

* `ex` の型は `forall A : Type, (A -> Prop) -> Prop`

* `exists x : A, P x` は `ex_intro` で生成されている。

* `ex_intro` の型は `forall (A : Type) (P : A -> Prop) (x : A), P x -> exists x, P x`

* `ex_ind` の型は `forall (A : Type) (P : A -> Prop) (P0 : Prop), (forall x : A, P x -> P0) -> (exists x, P x) -> P0`

であることが分かります。`ex_intro` と `ex_ind` の型が示す通り、
`exists x : A, P x` は集合論における直和 $\coprod _ {x \in A} P(x)$ に対応します。

`ex : forall A : Type, (A -> Prop) -> Prop` と `ex P : Prop` は整合性がとれていないように見えますが、
`Print ex.` の結果

    Inductive ex (A : Type) (P : A -> Prop) : Prop :=
        ex_intro : forall x : A, P x -> exists x, P x

    For ex: Argument A is implicit
    For ex_intro: Argument A is implicit
    For ex: Argument scopes are [type_scope _]
    For ex_intro: Argument scopes are [type_scope _ _ _]

の `For ex: Argument A is implicit` という記述から引数 `A` は明記する必要がないことが分かります。
(逆に明示的に `ex A P` などとするとエラーとなる。)
命題論理のページでちょくちょく出てきた `forall` などを都合よく無視できたのも同様の理由です。

具体例を見てみましょう。

    Lemma forall_exists : (forall x : A, P x -> Q x) -> (exists x : A, P x) -> (exists y : A, Q y).
    Proof.
      move => g.
      case.
      move => x px.
      apply ex_intro with x. (* exists x. *)
      apply g.
      apply px.
    Qed.

`case.` (この場合は `apply ex_ind.` としてもよい。) によって、
subgoal が `(exists x : A, P x) -> exists y : A, Q y` から
`forall x : A, P x -> exists y : A, Q y` に置き換わります。

Tips: `exists y : A, Q y` の形の subgoal を
`apply ex_intro with x.` によって、
`Q x` に置き換えられました。
これは `exists x.` に書き換えられます。

---

[Back](propositional.html) [Top](index.html)
