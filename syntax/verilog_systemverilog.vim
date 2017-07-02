" Vim syntax file
" Language: SystemVerilog

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
    syntax clear
elseif exists("b:current_syntax")
    finish
endif

" Set the local value of the 'iskeyword' option.
" NOTE: '?' was added so that verilogNumber would be processed correctly when
"       '?' is the last character of the number.
if version >= 600
   setlocal iskeyword=@,48-57,63,_,192-255
else
   set      iskeyword=@,48-57,63,_,192-255
endif

" Store cpoptions
let oldcpo=&cpoptions
set cpo-=C

" the order actually matters here! Keep vlog_pre as early as possible, at
" least before all other preprocessor commands
syn match   vlog_pre          "`[a-zA-Z0-9_]\+\>"

syn match   vlog_preproc      "`timescale"

syn match   vlog_include      "`include"

syn match   vlog_define       "`define"
syn match   vlog_define       "`undef"

syn match   vlog_precondit    "`ifdef"
syn match   vlog_precondit    "`ifndef"
syn match   vlog_precondit    "`else"
syn match   vlog_precondit    "`elsif"
syn match   vlog_precondit    "`endif"

" less used stuff
syn match   vlog_preproc      "`celldefine"
syn match   vlog_preproc      "`endcelldefine"
syn match   vlog_preproc      "`default_nettype"
syn match   vlog_preproc      "`line"
syn match   vlog_preproc      "`nounconnected_drive"
syn match   vlog_preproc      "`resetall"
syn match   vlog_preproc      "`unconnected_drive"

syn keyword vlog_port         input output inout

syn keyword vlog_type         logic reg wire bit tri
syn keyword vlog_type         int integer unsigned signed
syn keyword vlog_type         byte
syn keyword vlog_type         shortint shortreal
syn keyword vlog_type         longint
syn keyword vlog_type         real realtime time
syn keyword vlog_type         mailbox event chandle string
syn keyword vlog_type         void

syn keyword vlog_structure    enum union struct
syn keyword vlog_structure    class endclass package endpackage program endprogram
syn keyword vlog_structure    interface endinterface modport clocking endclocking
syn keyword vlog_structure    checker endchecker config endconfig
syn keyword vlog_structure    module endmodule table endtable
syn keyword vlog_structure    primitive endprimitive
syn keyword vlog_storageclass virtual packed local protected const
syn keyword vlog_storageclass extends implements
syn keyword vlog_storageclass parameter localparam genvar
syn keyword vlog_typedef      typedef
syn keyword vlog_modifier     context pure export import automatic extern static

syn keyword vlog_special      timeprecision timeunit
syn keyword vlog_special      design liblist instance use cell

syn keyword vlog_conditional  if else case endcase casex casez
syn keyword vlog_conditional  inside unique unique0 priority
syn keyword vlog_conditional  generate endgenerate
syn keyword vlog_repeat       forever repeat while for do foreach
syn keyword vlog_label        return continue break default

syn keyword vlog_statement    assign deassign alias force release
syn keyword vlog_statement    new
syn keyword vlog_process      always always_latch always_ff always_comb
syn keyword vlog_process      initial final

syn match   vlog_constant     "\<[A-Z][A-Z0-9_]\+\>"

syn match   vlog_time         "#[0-9]\+\(fs\|ps\|ns\|us\|ms\|s\)\=\>"

syn match   vlog_number       "\(\<\d\+\|\)'[sS]\?[bB]\s*[0-1_xXzZ?]\+\>"
syn match   vlog_number       "\(\<\d\+\|\)'[sS]\?[oO]\s*[0-7_xXzZ?]\+\>"
syn match   vlog_number       "\(\<\d\+\|\)'[sS]\?[dD]\s*[0-9_xXzZ?]\+\>"
syn match   vlog_number       "\(\<\d\+\|\)'[sS]\?[hH]\s*[0-9a-fA-F_xXzZ?]\+\>"
syn match   vlog_number       "\<[+-]\=[0-9_]\+\(\.[0-9_]*\|\)\(e[0-9_]*\|\)\>"

syn keyword vlog_sensitivity  edge posedge negedge

syn match   vlog_operator     "[&|~><!)(*%@+/=?:;}{,.\^\-\[\]]"
syn match   vlog_operator     "\<implies\>"
syn keyword vlog_keyword      null this super

syn keyword vlog_control      fork join join_any join_none forkjoin

syn match   vlog_function     "\$\=\(\s\+\.\)\@<!\<\w\+\ze("

" a bunch of "deprecated" keywords. e.g. defparam is pretty much considered
" evil in modern code. However, one might encounter it in library code or
" legacy code
syn keyword vlog_discouraged  defparam macromodule

syn region  vlog_string start=+"+ skip=+\\"+ end=+"+ contains=vlog_escape,@Spell
syn match   vlog_escape +\\[nt"\\]+ contained
syn match   vlog_escape "\\\o\o\=\o\=" contained

syn case ignore
syn keyword vlog_todo         contained TODO FIXME XXX
syn case match
syn match   vlog_comment      "//.*" contains=vlog_todo,@Spell,vlog_bad_newline

" space after a \
" This is dangerous as most compilers will not treat the \ as a
" line-continuation
syn match	  vlog_bad_newline           "\\\s\+$"
syn match	  vlog_bad_newline contained "\\\s\+$"

" really weird and mostly unused verilog keywords, thus not enabled by default
if exists("g:vlog_all_keyword")
    syn keyword vlog_keyword2  and buf bufif0 bufif1 cmos nand nmos nor not
    syn keyword vlog_keyword2  notif0 notif1 or pmos pull0 pull1 pulldown
    syn keyword vlog_keyword2  pullup wand wor xnor xor rcmos rnmos rpmos
    syn keyword vlog_keyword2  rtran rtranif0 rtranif1 supply0
    syn keyword vlog_keyword2  supply1 tran tranif0 tranif1 tri0 tri1 triand
    syn keyword vlog_keyword2  trior trireg
    syn keyword vlog_keyword2  weak weak0 weak1 strong strong0 strong1 highz0 highz1
    syn keyword vlog_keyword2  large medium small

    " specify
    syn keyword vlog_keyword2  specify endspecify showcancelled noshowcancelled
    syn keyword vlog_keyword2  pulsestyle_onevent pulsestyle_ondetect
    syn keyword vlog_keyword2  ifnone

    hi default link vlog_keyword2     Keyword
endif

syn keyword vlog_assert        assert assume restrict expect
syn keyword vlog_keyword       accept_on reject_on
syn keyword vlog_keyword       sync_accept_on sync_reject_on
syn keyword vlog_keyword       eventually nexttime until until_with
syn keyword vlog_keyword       s_eventually s_nexttime s_until s_until_with
syn keyword vlog_keyword       s_always
syn keyword vlog_keyword       intersect first_match throughout within
syn keyword vlog_keyword       triggered matched iff disable

syn region  vlog_em_script   start="//\s*synopsys\s\+dc_script_begin\>" end="//\s*synopsys\s\+dc_script_end\>"

hi default link vlog_pre          Macro
hi default link vlog_preproc      PreProc
hi default link vlog_include      Include
hi default link vlog_define       Define
hi default link vlog_precondit    PreCondit

hi default link vlog_port         StorageClass
hi default link vlog_type         Type
hi default link vlog_structure    Structure
hi default link vlog_storageclass StorageClass
hi default link vlog_typedef      Typedef nettype

hi default link vlog_modifier     Type

hi default link vlog_special      Special

hi default link vlog_statement    Statement
hi default link vlog_process      Statement
hi default link vlog_conditional  Conditional
hi default link vlog_repeat       Repeat
hi default link vlog_label        Label

hi default link vlog_constant     Constant
hi default link vlog_number       Number
hi default link vlog_time         Number

hi default link vlog_sensitivity  Keyword

hi default link vlog_operator     Operator
hi default link vlog_keyword      Keyword

hi default link vlog_control      Label
hi default link vlog_assert       Exception

hi default link vlog_function     Function

hi default link vlog_todo         Todo
hi default link vlog_comment      Comment
hi default link vlog_em_script    SpecialComment

hi default link vlog_string       String
hi default link vlog_escape       Special

hi default link vlog_discouraged  Error
hi default link vlog_bad_newline  Error

" A bunch of useful Verilog keywords







"##########################################################
"       SystemVerilog Syntax
"##########################################################

syn keyword verilogStatement   incdir include
syn keyword verilogStatement   library
syn keyword verilogStatement   scalared
syn keyword verilogStatement   specparam
syn keyword verilogStatement   vectored wait

syn keyword verilogStatement   rand randc constraint randomize
syn keyword verilogStatement   with dist
syn keyword verilogStatement   randcase
syn keyword verilogStatement   randsequence
syn keyword verilogStatement   get_randstate set_randstate
syn keyword verilogStatement   srandom
syn keyword verilogStatement   cover coverpoint
syn keyword verilogStatement   bins binsof illegal_bins ignore_bins
syn keyword verilogStatement   matches solve 
syn keyword verilogStatement   before bind
syn keyword verilogStatement   tagged 
syn keyword verilogStatement   type
syn keyword verilogStatement   uwire var cross ref wait_order 
syn keyword verilogStatement   wildcard 
syn keyword verilogStatement   std
syn keyword verilogStatement   interconnect let soft
syn keyword verilogStatement   untyped


" Only enable folding if g:verilog_syntax_fold is defined
if exists("g:verilog_syntax_fold")
    let s:verilog_syntax_fold=split(g:verilog_syntax_fold, ",")
else
    let s:verilog_syntax_fold=[]
endif

" Expand verilogComment
if len(s:verilog_syntax_fold) > 0
    if index(s:verilog_syntax_fold, "comment") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
        syn region  verilogComment  start="/\*"     end="\*/"   contains=verilogTodo,@Spell                     keepend fold
    else
        syn region  verilogComment  start="/\*"     end="\*/"   contains=verilogTodo,@Spell                     keepend
    endif
endif

if index(s:verilog_syntax_fold, "task") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\(\(\(extern\s\+\(\(pure\s\+\)\?virtual\s\+\)\?\)\|\(\pure\s\+virtual\s\+\)\)\(\(static\|protected\|local\)\s\+\)\?\)\@<!\<task\>"
        \ end="\<endtask\>"
        \ transparent
        \ keepend
        \ fold
    syn match   verilogStatement "\(\(\(extern\s\+\(\(pure\s\+\)\?virtual\s\+\)\?\)\|\(\pure\s\+virtual\s\+\)\)\(\(static\|protected\|local\)\s\+\)\?\)\@<=\<task\>"
else
    syn keyword verilogStatement  task endtask
endif

if index(s:verilog_syntax_fold, "function") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\(\(\(extern\s\+\(\(pure\s\+\)\?virtual\s\+\)\?\)\|\(\pure\s\+virtual\s\+\)\)\(\(static\|protected\|local\)\s\+\)\?\)\@<!\<function\>"
        \ end="\<endfunction\>"
        \ transparent
        \ keepend
        \ fold
    syn match   verilogStatement "\(\(\(extern\s\+\(\(pure\s\+\)\?virtual\s\+\)\?\)\|\(\pure\s\+virtual\s\+\)\)\(\(static\|protected\|local\)\s\+\)\?\)\@<=\<function\>"
else
    syn keyword verilogStatement  function endfunction
endif

if index(s:verilog_syntax_fold, "covergroup") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<covergroup\>"
        \ end="\<endgroup\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement  covergroup endgroup
endif

if index(s:verilog_syntax_fold, "sequence") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<sequence\>"
        \ end="\<endsequence\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement  sequence endsequence
endif

if index(s:verilog_syntax_fold, "property") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogStatement
        \ start="\<property\>"
        \ end="\<endproperty\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogStatement  property endproperty
endif

if index(s:verilog_syntax_fold, "specify") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogLabel
        \ start="\<specify\>"
        \ end="\<endspecify\>"
        \ transparent
        \ keepend
        \ fold
else
    syn keyword verilogLabel      specify endspecify
endif

if index(s:verilog_syntax_fold, "block") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region  verilogFold
        \ matchgroup=verilogLabel
        \ start="\<begin\>"
        \ end="\<end\>"
        \ transparent
        \ fold
else
    syn keyword verilogLabel      begin end
endif

if index(s:verilog_syntax_fold, "define") >= 0 || index(s:verilog_syntax_fold, "all") >= 0
    syn region verilogFoldIfContainer
        \ start="`ifn\?def\>"
        \ end="`endif\>"
        \ skip="/[*/].*"
        \ transparent
        \ keepend extend
        \ containedin=ALLBUT,verilogComment
        \ contains=NONE
    syn region verilogFoldIf
        \ start="`ifn\?def\>"
        \ end="^\s*`els\(e\|if\)\>"ms=s-1,me=s-1
        \ fold transparent
        \ keepend
        \ contained containedin=verilogFoldIfContainer
        \ nextgroup=verilogFoldElseIf,verilogFoldElse
        \ contains=TOP
    syn region verilogFoldElseIf
        \ start="`els\(e\|if\)\>"
        \ end="^\s*`els\(e\|if\)\>"ms=s-1,me=s-1
        \ fold transparent
        \ keepend
        \ contained containedin=verilogFoldIfContainer
        \ nextgroup=verilogFoldElseIf,verilogFoldElse
        \ contains=TOP
    syn region verilogFoldElse
        \ start="`else\>"
        \ end="`endif\>"
        \ fold transparent
        \ keepend
        \ contained containedin=verilogFoldIfContainer
        \ contains=TOP
    " The above syntax regions start/end matches will disable the respective
    " verilogGlobal keywords. This syntax match fixes that:
    syn match verilogGlobal "\<`\(ifn\?def\|e\(els\(e\|if\)\)\|ndif\)\>"
endif

"Modify the following as needed.  The trade-off is performance versus
"functionality.
syn sync minlines=50


" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_verilog_syn_inits")
    if version < 508
        let did_verilog_syn_inits = 1
        command -nargs=+ HiLink hi link <args>
    else
        command -nargs=+ HiLink hi def link <args>
    endif

    " The default highlighting.
    HiLink verilogCharacter       Character
    HiLink verilogConditional     Conditional
    HiLink verilogRepeat          Repeat
    HiLink verilogString          String
    HiLink verilogTodo            Todo
    HiLink verilogComment         Comment
    HiLink verilogConstant        Constant
    HiLink verilogLabel           Label
    HiLink verilogNumber          Number
    HiLink verilogOperator        Special
    HiLink verilogStatement       Statement
    HiLink verilogGlobal          Define
    HiLink verilogEscape          Special
    HiLink verilogMethod          Function
    HiLink verilogTypeDef         TypeDef
    HiLink verilogAssertion       Include
    HiLink verilogObject          Type

    delcommand HiLink
endif

let b:current_syntax = "verilog_systemverilog"

" Restore cpoptions
let &cpoptions=oldcpo
