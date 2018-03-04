" Vim syntax file
" Language:        SubML
" Maintainer:      Rodolphe Lepigre <rodolphe.lepigre@inria.fr>
" Last Change:     03/03/2018
" Version:         1.0
" Original Author: Rodolphe Lepigre <rodolphe.lepigre@inria.fr>

if exists("b:current_syntax")
  finish
endif

" Comments
sy keyword CommentTags contained TODO FIXME NOTE
sy region string start=+"+ skip=+\\\\\|\\"+ end=+"+ oneline
sy region SubMLComment start="(\*" end="\*)" contains=CommentTags,string
hi link SubMLComment  Comment
hi link CommentTags Todo

" Special
sy match SubMLSpecial "set [a-z]* [a-z]*"
hi link SubMLSpecial Include

" Latex
sy include @tex syntax/tex.vim
sy region texCode matchgroup=Include start="latex\s*{" end="}" contains=@tex

" Keywords
sy keyword SubMLKeyword val rec fun case of fix if then else with let in
sy keyword SubMLKeyword type such that abort include eval check set graphml

hi link SubMLKeyword Keyword

" Special elements
sy match SubMLOperator display "λ"
sy match SubMLOperator display "\."
sy match SubMLOperator display "→"
sy match SubMLOperator display "×"
sy match SubMLOperator display ";"
sy match SubMLOperator display ":"
sy match SubMLOperator display "|"
sy match SubMLOperator display "="
sy match SubMLOperator display "μ"
sy match SubMLOperator display "ν"
sy match SubMLOperator display "∀"
sy match SubMLOperator display "∃"
sy match SubMLOperator display "\["
sy match SubMLOperator display "\]"
sy match SubMLOperator display "{"
sy match SubMLOperator display "}"
sy match SubMLOperator display "⊆"
hi link SubMLOperator Special

" A few functions to work with abbreviations (input mode).
func Eatspace()
  let c = nr2char(getchar(0))
  return (c =~ '\s') ? '' : c
endfunc

function! s:Expr(default, repl)
  if getline('.')[col('.')-2]=='\'
    return "\<bs>".a:repl
  else
    return a:default
  endif
endfunction

function! s:DefAB(lhs, rhs)
  exe 'ab '.a:lhs.' <c-r>=<sid>Expr('.string(a:lhs).', '.string(a:rhs).')<cr>'
endfunction

function! s:DefABEat(lhs, rhs)
  exe 'ab '.a:lhs.' <c-r>=<sid>Expr('.string(a:lhs).', '.string(a:rhs).')<cr><c-r>=Eatspace()<cr>'
endfunction

command! -nargs=+ ABBackslash    call s:DefAB(<f-args>)
command! -nargs=+ ABBackslashEat call s:DefABEat(<f-args>)

" Usual abbreviations.
ab ->      →
ab \\      λ<c-r>=Eatspace()<cr>

" Abbreviations starting with backslash.
ABBackslash    to      →
ABBackslash    in      ∈
ABBackslash    notin   ∉
ABBackslash    times   ×
ABBackslashEat lambda  λ
ABBackslashEat forall  ∀
ABBackslashEat exists  ∃
ABBackslash    sub     ⊆
ABBackslash    infty   ∞
ABBackslashEat mu      μ
ABBackslashEat nu      ν
ABBackslash    alpha   α
ABBackslash    beta    β
ABBackslash    gamma   γ
ABBackslash    delta   δ
ABBackslash    epsilon ε
ABBackslash    dots    …
