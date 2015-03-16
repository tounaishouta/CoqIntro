% 証明支援システム Coq の紹介

Coq とは
--------

詳しい説明は [Wikipedia](https://ja.wikipedia.org/wiki/Coq) や
[本家 (英語)](https://coq.inria.fr/) に譲って簡単に説明すると、
Coq とは **正しい事を機械的に確認できる証明** を人間が書く手助けをするシステムです。

[四色定理](http://ja.wikipedia.org/wiki/四色定理) や
[Feit-Thompson theorem](http://en.wikipedia.org/wiki/Feit–Thompson_theorem) など
人間では困難な証明の確認を機械的に実行するのに用いられているようです。

目的
----

ここでは Coq の基本的な使い方をごく簡単に紹介します。

より詳しい情報については以下を参照してください。

* [A short introduction to Coq (英語)](https://coq.inria.fr/a-short-introduction-to-coq)
* [The Coq Proof Asistant A Tutorial (英語, pdf)](http://flint.cs.yale.edu/cs430/coq/pdf/Tutorial.pdf)
* [名古屋大学講義資料](http://www.math.nagoya-u.ac.jp/~garrigue/lecture/2009_AW/index.html)
* [プログラミング Coq](http://www.iij-ii.co.jp/lab/techdoc/coqt/)

インストール
------------

Debian, Ubuntu などの場合は、端末から

    $ sudo apt-get install coq libssreflect-coq

を実行します。

Windows, OS X に関しては
[こちらの記事](http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt1.html)
が参考になると思います。

目次
----

* [動かしてみる](tutorial.html)
* [エディタ](editor.html)
* [命題論理](propositional.html)
* [述語論理](predicate.html)
