(provide 'subml-mode)

(defvar subml-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [foo] 'subml-do-foo)
    map)
  "Keymap for `subml-mode'.")

(defvar subml-mode-syntax-table
  (let ((subml-mode-syntax-table (make-syntax-table)))

    ; This is added so entity names with underscores can be more easily parsed
    (modify-syntax-entry ?_ "w" subml-mode-syntax-table)
    (modify-syntax-entry ?' "w" subml-mode-syntax-table)

    ; Comment styles are same as C++
    (modify-syntax-entry ?\) ")(4" subml-mode-syntax-table)
    (modify-syntax-entry ?* ". 23" subml-mode-syntax-table)
    (modify-syntax-entry ?\( "()1" subml-mode-syntax-table)
    ;       (modify-syntax-entry ?\n "> b" subml-mode-syntax-table)
    subml-mode-syntax-table)
  "Syntax table for subml-mode")

(defconst subml-font-lock-keywords
  (list (cons (concat "\\<"
		      (regexp-opt '("case" "of" "val" "let" "in" "rec" "fun" "eval"
				    "include" "type" "if" "then" "else" "check"))
                      "\\>")
              'font-lock-keyword-face)
        )
  "Minimal highlighting expressions for subml mode.")

(require 'quail)
(quail-define-package
 "Subml" "Subml" "x⃗" t
 "A transliteration scheme for Subml."
 nil t t t t nil t nil nil nil t)
(quail-define-rules
 ("\\mu" ?μ)
 ("\\nu" ?ν)
 ("\\all" ?∀)
 ("\\exists" ?∃)
 ("->" ?→)
 ("\\times" ?×)
 ("\\sub" ?⊂))


 ;;;###autoload
(define-derived-mode subml-mode fundamental-mode "Subml"
  "A major mode for editing Subml files."
  :syntax-table subml-mode-syntax-table
  (setq-local font-lock-defaults
              '(subml-font-lock-keywords))
  (setq-local indent-line-function 'subml-indent-line)
  (set-input-method "Subml")
                                        ;(setq-local imenu-generic-expression
                                        ;subml-imenu-generic-expression)
                                        ;(setq-local outline-regexp subml-outline-regexp)
  )

 ;;; Indentation

                                        ; (defun subml-indent-line ()
                                        ;   "Indent current line of Subml code."
                                        ;   (interactive)
                                        ;   (let ((savep (> (current-column) (current-indentation)))
;;       (indent (condition-case nil (max (subml-calculate-indentation) 0)
;;                 (error 0))))
;;     (if savep
;;       (save-excursion (indent-line-to indent))
;;       (indent-line-to indent))))

;; (defun subml-calculate-indentation ()
;;   "Return the column to which the current line should be indented."
;;   ...)

(add-to-list 'auto-mode-alist '("\\.typ\\'" . subml-mode))

 ;;; subml.el ends here
