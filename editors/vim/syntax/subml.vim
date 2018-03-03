" Vim syntax file
" Language:        SubML
" Maintainer:      Rodolphe Lepigre <rodolphe.lepigre@univ-savoie.fr>
" Last Change:     21/07/2016
" Version:         1.0
" Original Author: Rodolphe Lepigre <rodolphe.lepigre@univ-savoie.fr>

if exists("b:current_syntax")
  finish
endif

" Comments
syn keyword CommentTags contained TODO FIXME NOTE
syn region string start=+"+ skip=+\\\\\|\\"+ end=+"+ oneline
syn region SubMLComment start="(\*" end="\*)" contains=CommentTags,string
hi link SubMLComment  Comment
hi link CommentTags Todo

" Special
syntax match PMLSpecial "set [a-z]* [a-z]*"
highlight link PMLSpecial Include

" Latex
syn include @tex syntax/tex.vim
syn region texCode matchgroup=Include start="latex\s*{" end="}" contains=@tex

" Keywords
syntax keyword PMLKeyword val rec type eval include check such that
syntax keyword PMLKeyword fun case of fix if then else match with let in

highlight link PMLKeyword Keyword

" Special elements
syntax match PMLOperator display "λ"
syntax match PMLOperator display "\."
syntax match PMLOperator display "→"
syntax match PMLOperator display "×"
syntax match PMLOperator display "↦"
syntax match PMLOperator display ";"
syntax match PMLOperator display ":"
syntax match PMLOperator display "|"
syntax match PMLOperator display "="
syntax match PMLOperator display "μ"
syntax match PMLOperator display "ν"
syntax match PMLOperator display "∀"
syntax match PMLOperator display "∃"
syntax match PMLOperator display "χ"
syntax match PMLOperator display "\["
syntax match PMLOperator display "\]"
syntax match PMLOperator display "{"
syntax match PMLOperator display "}"
syntax match PMLOperator display "⊆"
syntax match PMLOperator display "≡"
syntax match PMLOperator display "✂"
hi link PMLOperator Special
