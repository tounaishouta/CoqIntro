% 命題論理

このページでは命題論理の証明について見て行きましょう。

[説明に用いるスクリプトや演習の解答例](src/propositional.v)

[動かしてみる](tutorial.html) のページで論理包含 `->` について詳しく見ました。
実は他の論理演算についても、この `->` を用いて定義されています。

論理和 `\/`
-----------

最初に論理和についてです。
`\/` により $\lor$ を表現しているのですが、
環境によってはバックスラッシュ＼が円記号￥として
表示されてしまうようです。
次のコマンドを実行して
論理和の定義を見て行きましょう。

    Require Import ssreflect.

    Section Propositional.

      Variable A B C : Prop.

      Section Disjunction.

        Locate "\/".

新しく始めていますが、`End Tutorial.` の続きから始めても構いません。
CoqIDE の場合 `Locate`, `Check`, `Print` はスクリプトの中で直接実行すると
警告が出るのですが、説明の都合上警告は無視してこのスタイルで進めることにします。
気になる人は前々回用いた Query Pane を使ってください。

実行結果

    Notation            Scope
    "A \/ B" := or A B   : type_scope
                          (default interpretation)

から `A \/ B` というのは `or A B` の書き換えであるとわかります。

続けて

    Check or.

を実行すると、`or` の型が `Prop -> Prop -> Prop` であることが分かります。
すなわち、`or` は命題２つを引数にとり命題を返す関数です。

`or` の定義は

    Print or.

で確認できます。
色々書いてありますが大事なのは最初の部分

    Inductive or (A B : Prop) : Prop :=
        or_introl : A -> A \/ B | or_intror : B -> A \/ B

で、意味するところは、`or A B` (`A \/ B`) というのは `or_introl : A -> A \/ B` と
`or_intror : B -> A \/ B` で「自由に生成された」命題だということです。
この `or_introl` や `or_intror` は `or A B` (`A \/ B`) の constructor と呼ばれます。

`Inductive` Command で定義された型には、`名前_ind` という関数が付随します。
`or_introl`, `or_intror`, `or_ind` の型を `Check` Command で見てみると、

    or_introl : forall A B : Prop, A -> A \/ B
    or_intror : forall A B : Prop, B -> A \/ B
    or_ind    : forall A B P : Prop, (A -> P) -> (B -> P) -> (A \/ B -> P)

となっていることが分かります。
(`Check` Command は型を確認する Command です。)
`forall ... ,` の部分を適度に無視して、集合論の言葉で言い換えて説明すると、

* `A` から `A \/ B` に写像がある。
* `B` から `A \/ B` に写像がある。
* 任意の `P` に対して、「`A` から `P` への写像」と「`B` から `P` への写像」から
  「`A \/ B` から `P` への写像」が得られる。

というようなことを言っているわけです。
これはまさに集合の disjoint union の普遍性ですよね。
実際、論理和 `A \/ B` は型システムの直和型 `A + B` に対応します。
先ほど述べた「自由に生成された」の意味を感じていただけでしょうか。
`forall ... ,` については [述語論理](predicate.html) のページで解説したいと思います。

この普遍性を用いて論理和の結合性をを証明してみます。

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

`\/` は右結合なので、`A \/ B \/ C` と表示されていたら、`A \/ (B \/ C)` の意味です。

Tips:
`A \/ B -> P` の形の subgoal を
`apply or_ind.` によって、
`A -> P` と `B -> P` の２つの subgoal に分割できました。
この場合分けを賢く行ってくれるのが `case` tactic です。
上の証明の `apply or_ind.` は２つとも `case.` に書き換えられます。
`case` は `\/` 以外の場合にも使える便利な tactic です。

Tips:
`A \/ B` の形の subgoal を
`apply or_introl.` や `apply or_intror.` によって、
`A` や `B` に置き換えられました。
これらはそれぞれ `left.` や `right.` に書き換えられます。

### 演習

同様に

    Lemma or_trans' : A \/ (B \/ C) -> (A \/ B) \/ C.

    Lemma or_comm : A \/ B -> B \/ A.

    Lemma or_iden : A \/ A -> A.

を示してみましょう。

論理積 `/\`
-----------

前回と同様に論理積についてみ見てみましょう。

    Section Conjunction.

      Locate "/\".

      Check and.

      Print and.

      Check conj.
      Check and_ind.

すると、

* `A /\ B` は `and A B` の書き換え

* `and` の型は `Prop -> Prop -> Prop`

* `and A B` (`A /\ B`) は `conj : A -> B -> A /\ B` で
  「自由に生成された」型

* `conj` の型は `forall A B : Prop, A -> B -> A /\ B`

* `and_ind` の型は `forall A B P : Prop, (A -> B -> P) -> A /\ B -> P`

であることが分かります。これを直積の普遍性というのは少し苦しい感じもしますが、
(closed monoidal category の言葉で説明できるかもしれませんが・・・)
型システムにおける直積型 `A * B` に対応しています。

基本的な命題を示してみましょう。
`/\` が subgoal の仮定にあるときも同様に `case` tactic が使えます。

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

Tips: `A /\ B` の形の subgoal を `apply conj.` によって、
`A` と `B` の2つの subgoal に分割できました。
これは `split.` に書き換えられます。
`split` は `/\` 以外の場合も constructor がひとつならば使える
便利な tactic です。

### 演習

同様に

    Lemma and_elimr : A /\ B -> B.

    Lemma and_trans : (A /\ B) /\ C -> A /\ (B /\ C).

    Lemma and_trans' : A /\ (B /\ C) -> (A /\ B) /\ C.

    Lemma and_iden : A -> A /\ A.

を示しましょう。

論理否定 `~`
------------

次に論理否定についてみ見てみましょう。

    Section Negation.

      Locate "~".
      Check not.
      Print not.

      Check False.
      Print False.
      Check False_ind.

実行結果を順に見ていくと、

* `~ x` は `not x` の書き換え
* `not` の型は `Prop -> Prop`
* `not` は `A : Prop` に `A -> False` を対応させる関数

であることが分かります。
`False` が何か調べてみると、少し面白いことになっていて
`False` は何もないところから「自由に生成された」命題であることが分かります。
`False` は「偽」を表す命題で、
型システムにおけるボトム型、集合論における空集合に対応します。
`False_ind` の型から `False -> P` の形の subgoal は
`apply False_ind.` または単に `case.` とすることで即座に導出できることが分かります。
それ以外の形の subgoal は `apply False_ind.` とすることで、
`False` に置き換えられます。
矛盾が導けるならばなんでも導出できるということです。

[選言三段論法](http://ja.wikipedia.org/wiki/選言三段論法) を示してみましょう。

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

新しく `unfold` tactic が出てきたので説明しておきます。
上で見たように `~ A` は `not A` のことで、
`not` は `A` に `A -> False` を対応させる関数だったので、
`~ A` は `A -> False` と同値です。
`unfold "~".` とすることでこの書き換えを行ってくれます。

Tips: `apply False_ind.` によって、
subgoal を `False` に置き換えられました。
これは `exfalso.` に書き換えられます。
ラテン語の [ex falso quodlibet](http://en.wikipedia.org/wiki/Principle_of_explosion)
に由来しています。

次に二重否定の導入を示してみましょう。

    Lemma double_neg_intro : A -> ~ ~ A.
    Proof.
      unfold "~".
      move => a not_a.
      apply not_a.
      apply a.
    Qed.

今まで証明論と型システムの関係を見てきましたが
ここで扱っている論理は [直観論理](http://ja.wikipedia.org/wiki/直観論理)
と呼ばれるもので、
二重否定の除去、あるいは排中律を認めない立場をとっています。
それでは困る気もしますが、次を書けば万事解決します。

    Hypothesis double_neg_elim : forall P : Prop, ~ ~ P -> P.

`Hypothesis` とありますが、実は `Variable` と同じことで、
`double_neg_elim` を型 `forall P : Prop, ~ ~ P -> P` を持つ変数として
定義しているだけです。
この仮定のもとで排中律を示してみましょう。

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

### 演習

できるだけ `double_neg_elim` を用いずに

    Lemma triple_neg : ~ ~ ~ A -> ~ A.

    Lemma de_morgan_1 : ~ (A \/ B) -> (~ A /\ ~ B).

    Lemma de_morgan_1' : (~ A /\ ~ B) -> ~ (A \/ B).

    Lemma de_morgan_2 : ~ (A /\ B) -> (~ A \/ ~ B).

    Lemma de_morgan_2' : (~ A \/ ~ B) -> ~ (A /\ B).

    Lemma de_morgan_3 : (A -> B) -> (~ B -> ~ A).

    Lemma de_morgan_3' : (~ B -> ~ A) -> (A -> B).

を示してみましょう。

---

[Back](editor.html) [Top](index.html) [Next](predicate.html)
