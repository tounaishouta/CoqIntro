% エディタ

保存
----

長い証明を書くようになると当然書いたスクリプトを保存する必要が出てくると思います。
CoqIDE からも普通のエディタと同じ要領でファイルの保存、読み込みができます。
Coq のスクリプトファイルの拡張子は `.v` です。

以下の説明は Emacs か Vim を使っている人向けのものです。
そうでない人は残りは読み飛ばして次のページに進んでください。

Emacs
-----

Emacs には Coq 等の証明支援システムのための
[Proof Genaral](http://proofgeneral.inf.ed.ac.uk/)
という便利なプラグイン？があるようです。
筆者は Emacs は詳しくないので自分で調べてください。

Vim
---

Vim にも Coq 用の
[プラグイン](http://www.vim.org/scripts/script.php?script_id=4388)
があります。
が、これは Vim に `+perl` オプションが必要なようです。
筆者は `+perl` オプションといわれてもよくわからないレベルの Vimmer なので、
標準の Vim で使える簡易版の
[プラグイン](https://github.com/tounaishouta/coq.vim)
を作ってみました。

---

[Back](tutorial.html) [Top](index.html) [Next](propositional.html)
