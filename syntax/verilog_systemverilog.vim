" Vim syntax file
" Language: SystemVerilog (superset extension of Verilog)

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
   set iskeyword=@,48-57,63,_,192-255
endif

" A bunch of useful Verilog keywords


syn keyword verilogTodo contained TODO FIXME

syn match   verilogOperator "[&|~><!)(*#%@+/=?:;}{,.\^\-\[\]]"

"syn match   verilogGlobal "`[a-zA-Z0-9_]\+\>"
syn match   verilogGlobal "`celldefine"
syn match   verilogGlobal "`default_nettype"
syn match   verilogGlobal "`define"
syn match   verilogGlobal "`else"
syn match   verilogGlobal "`elsif"
syn match   verilogGlobal "`endcelldefine"
syn match   verilogGlobal "`endif"
syn match   verilogGlobal "`ifdef"
syn match   verilogGlobal "`ifndef"
syn match   verilogGlobal "`include"
syn match   verilogGlobal "`line"
syn match   verilogGlobal "`nounconnected_drive"
syn match   verilogGlobal "`resetall"
syn match   verilogGlobal "`timescale"
syn match   verilogGlobal "`unconnected_drive"
syn match   verilogGlobal "`undef"
syn match   verilogGlobal "$[a-zA-Z0-9_]\+\>"

syn match   verilogConstant "\<[A-Z][A-Z0-9_]\+\>"

syn match   verilogNumber "\(\<\d\+\|\)'[sS]\?[bB]\s*[0-1_xXzZ?]\+\>"
syn match   verilogNumber "\(\<\d\+\|\)'[sS]\?[oO]\s*[0-7_xXzZ?]\+\>"
syn match   verilogNumber "\(\<\d\+\|\)'[sS]\?[dD]\s*[0-9_xXzZ?]\+\>"
syn match   verilogNumber "\(\<\d\+\|\)'[sS]\?[hH]\s*[0-9a-fA-F_xXzZ?]\+\>"
syn match   verilogNumber "\<[+-]\=[0-9_]\+\(\.[0-9_]*\|\)\(e[0-9_]*\|\)\>"

syn region  verilogString start=+"+ skip=+\\"+ end=+"+ contains=verilogEscape,@Spell
syn match   verilogEscape +\\[nt"\\]+ contained
syn match   verilogEscape "\\\o\o\=\o\=" contained

" Directives
syn match   verilogDirective   "//\s*synopsys\>.*$"
syn region  verilogDirective   start="/\*\s*synopsys\>" end="\*/"
syn region  verilogDirective   start="//\s*synopsys dc_script_begin\>" end="//\s*synopsys dc_script_end\>"

syn match   verilogDirective   "//\s*\$s\>.*$"
syn region  verilogDirective   start="/\*\s*\$s\>" end="\*/"
syn region  verilogDirective   start="//\s*\$s dc_script_begin\>" end="//\s*\$s dc_script_end\>"


" Store cpoptions
let oldcpo=&cpoptions
set cpo-=C

syn sync lines=1000

"##########################################################
"       SystemVerilog Syntax
"##########################################################

syn keyword verilogStatement   always and assign automatic buf
syn keyword verilogStatement   bufif0 bufif1 cell cmos
syn keyword verilogStatement   config deassign defparam design
syn keyword verilogStatement   disable edge endconfig
syn keyword verilogStatement   endgenerate endmodule
syn keyword verilogStatement   endprimitive endtable
syn keyword verilogStatement   event force
syn keyword verilogStatement   generate genvar highz0 highz1 ifnone
syn keyword verilogStatement   incdir include initial inout input
syn keyword verilogStatement   instance integer large liblist
syn keyword verilogStatement   library localparam macromodule medium
syn keyword verilogStatement   module nand negedge nmos nor
syn keyword verilogStatement   noshowcancelled not notif0 notif1 or
syn keyword verilogStatement   output parameter pmos posedge primitive
syn keyword verilogStatement   pull0 pull1 pulldown pullup
syn keyword verilogStatement   pulsestyle_onevent pulsestyle_ondetect
syn keyword verilogStatement   rcmos real realtime reg release
syn keyword verilogStatement   rnmos rpmos rtran rtranif0 rtranif1
syn keyword verilogStatement   scalared showcancelled signed small
syn keyword verilogStatement   specparam strong0 strong1
syn keyword verilogStatement   supply0 supply1 table time tran
syn keyword verilogStatement   tranif0 tranif1 tri tri0 tri1 triand
syn keyword verilogStatement   trior trireg unsigned use vectored wait
syn keyword verilogStatement   wand weak0 weak1 wire wor xnor xor

syn keyword verilogStatement   always_comb always_ff always_latch
syn keyword verilogStatement   class endclass
syn keyword verilogStatement   checker endchecker
syn keyword verilogStatement   virtual local const protected
syn keyword verilogStatement   package endpackage
syn keyword verilogStatement   rand randc constraint randomize
syn keyword verilogStatement   with inside dist
syn keyword verilogStatement   randcase
syn keyword verilogStatement   randsequence
syn keyword verilogStatement   get_randstate set_randstate
syn keyword verilogStatement   srandom
syn keyword verilogStatement   logic bit byte time
syn keyword verilogStatement   int longint shortint
syn keyword verilogStatement   struct packed
syn keyword verilogStatement   final
syn keyword verilogStatement   import export
syn keyword verilogStatement   context pure
syn keyword verilogStatement   void shortreal chandle string
syn keyword verilogStatement   clocking endclocking
syn keyword verilogStatement   interface endinterface modport
syn keyword verilogStatement   cover coverpoint
syn keyword verilogStatement   program endprogram
syn keyword verilogStatement   bins binsof illegal_bins ignore_bins
syn keyword verilogStatement   alias matches solve static assert
syn keyword verilogStatement   assume before expect bind
syn keyword verilogStatement   extends null tagged extern this
syn keyword verilogStatement   first_match throughout timeprecision
syn keyword verilogStatement   timeunit priority type union
syn keyword verilogStatement   uwire var cross ref wait_order intersect
syn keyword verilogStatement   wildcard within
syn keyword verilogStatement   triggered
syn keyword verilogStatement   std
syn keyword verilogStatement   accept_on eventually global implements implies
syn keyword verilogStatement   interconnect let nettype nexttime reject_on restrict soft
syn keyword verilogStatement   s_always s_eventually s_nexttime s_until s_until_with
syn keyword verilogStatement   strong sync_accept_on sync_reject_on unique unique0
syn keyword verilogStatement   until until_with untyped weak


syn keyword verilogTypeDef     typedef enum

syn keyword verilogConditional if else case casex casez default endcase
syn keyword verilogConditional iff

syn keyword verilogRepeat      forever repeat while for
syn keyword verilogRepeat      return break continue
syn keyword verilogRepeat      do while foreach

syn keyword verilogLabel       fork join
syn keyword verilogLabel       join_any join_none forkjoin

syn match   verilogGlobal      "`begin_\w\+"
syn match   verilogGlobal      "`end_\w\+"
syn match   verilogGlobal      "`remove_\w\+"
syn match   verilogGlobal      "`restore_\w\+"

syn match   verilogGlobal      "`[a-zA-Z0-9_]\+\>"

syn match   verilogNumber      "\<\d[0-9_]*\(\.\?[0-9_]\+\)\=\([fpnum]\)\=s\>"
syn keyword verilogNumber      1step

syn keyword verilogMethod      new
syn match   verilogMethod      "\(\s\+\.\)\@<!\<\w\+\ze("

syn match   verilogAssertion   "\<\w\+\>\s*:\s*\<assert\>\_.\{-});"

syn keyword verilogObject      super
syn match   verilogObject      "\<\w\+\ze\(::\|\.\)" contains=verilogNumber

" Only enable folding if g:verilog_syntax_fold is defined
if exists("g:verilog_syntax_fold")
    let s:verilog_syntax_fold=split(g:verilog_syntax_fold, ",")
else
    let s:verilog_syntax_fold=[]
endif

" Expand verilogComment
syn match   verilogComment  "//.*"                      contains=verilogTodo,@Spell
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
    HiLink verilogDirective       SpecialComment
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

" vim: ts=8
