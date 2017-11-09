(TeX-add-style-hook
 "answer"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8x")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "ucs"
    "inputenc"
    "graphicx"
    "amsmath"
    "amsthm"
    "amssymb"
    "url"
    "stmaryrd"
    "ifpdf"
    "proof"))
 :latex)

