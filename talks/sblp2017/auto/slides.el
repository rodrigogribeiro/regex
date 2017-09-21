(TeX-add-style-hook
 "slides"
 (lambda ()
   (TeX-run-style-hooks
    "latex2e"
    "beamer"
    "beamer10"
    "graphicx"
    "booktabs"
    "color")
   (TeX-add-symbols
    '("V" 1)
    '("F" 1)
    '("C" 1)
    '("D" 1)
    '("brownBG" 1)
    '("yellowBG" 1)
    '("whiteFG" 1)
    '("blackFG" 1)
    '("brownFG" 1)
    '("yellowFG" 1)
    '("purpleFG" 1)
    '("orangeFG" 1)
    '("blueFG" 1)
    '("greenFG" 1)
    '("redFG" 1)
    "ColourStuff"
    "red"
    "green"
    "blue"
    "orange"
    "purple"
    "yellow"
    "brown"
    "black"
    "white"
    "MonochromeStuff")
   (LaTeX-add-environments
    "Lemma"
    "Theorem"
    "Example"))
 :latex)

