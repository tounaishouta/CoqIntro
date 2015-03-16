build:
	pandoc -s -c style.css --mathjax -o ../index.html index.md
	pandoc -s -c style.css --mathjax -o ../tutorial.html tutorial.md
	pandoc -s -c style.css --mathjax -o ../editor.html editor.md
	pandoc -s -c style.css --mathjax -o ../propositional.html propositional.md
	pandoc -s -c style.css --mathjax -o ../predicate.html predicate.md

run:
	firefox ../index.html &
