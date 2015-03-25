;;; package --- Summary
;;; A major mode for editing Insomnia programs.
;;;
;;; Commentary:
;;;
;;; Setup:
;;;   (add-to-path "[gitroot]/emacs")
;;;   (require 'insomnia-mode)
;;;
;;; Code:
(require 'generic)

(defvar insomnia-mode-tab-width 2
  "The indentation width for insomnia-mode.")
(defun insomnia-mode-indentation ()
  "Set up the indentation for insomnia-mode."
  (progn (setq tab-width insomnia-mode-tab-width)
         (setq indent-tabs-mode nil)))

(unless (fboundp 'insomnia-mode)
  (define-generic-mode 'insomnia-mode
    '(("--" . nil))
    '("module" "model"
      "query"
      "type" "sig" "where"
      "fun" "val"
      "let" "in" "end"
      "forall" "∀"
      "infix" "infixl" "infixr"
      "import" "local"
      "data" "enum"
      "parameter" "random"
      "return"
      "case" "of"
      "assume")
    
    '(("\\_<[[:upper:]]\\(\\s_\\|[[:upper:]]\\)+\\_>" . 'font-lock-constant-face) ;; module types
      ("\\_<[[:upper:]]\\(\\s_\\|\sw\\)+\\_>" . 'font-lock-type-face)
      ) ; font-lock-keywords
    (list "\\.ism\\'")
    (list 'insomnia-mode-indentation)
    "Major mode for editing Insomnia programs"))

(provide 'insomnia-mode)
;;; insomnia-mode ends here

