(TeX-add-style-hook
 "pts"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("geometry" "top=1cm" "bottom=1.5cm" "outer=4.5cm" "inner=1cm" "heightrounded" "marginparwidth=3.5cm" "marginparsep=0.5cm") ("biblatex" "backend=biber")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "StandardTemplate"
    "StandardTemplate10"
    "bussproofs"
    "tikz-cd"
    "stmaryrd"
    "enumitem"
    "xcolor"
    "geometry"
    "biblatex")
   (TeX-add-symbols
    '("specialcell" 1)
    '("pushright" 1)
    '("citemargin" 1)
    '("margincom" 1)
    '("gray" 1)
    "Type"
    "Kind"
    "Set"
    "Prop"
    "N"
    "red"
    "nType"
    "nKind"
    "nSet"
    "nProp"
    "Lvl"
    "suc"
    "set"
    "Prf"
    "El"
    "U"
    "Sort"
    "Level"
    "ctx"
    "Nn")
   (LaTeX-add-labels
    "sec:pts"
    "sec:apts"
    "sec:sound"
    "sec:cons"
    "sec:encoding"
    "subsec:sound"
    "subsec:meta"
    "sec:label"
    "subsec:def"
    "sec:nonprenex"
    "subsec:label"
    "sec:enc"
    "subsec:correct")
   (LaTeX-add-environments
    "claim")
   (LaTeX-add-bibliographies)
   (LaTeX-add-counters
    "margincount")
   (LaTeX-add-xcolor-definecolors
    "mygray"))
 :latex)

