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

syn keyword vlog_type         logic reg wire uwire bit tri
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
syn keyword vlog_structure    task endtask function endfunction
syn keyword vlog_storageclass virtual packed tagged local protected const ref
syn keyword vlog_storageclass extends implements
syn keyword vlog_storageclass parameter localparam specparam genvar
syn keyword vlog_typedef      typedef nettype
syn keyword vlog_modifier     context pure export import automatic extern static

syn keyword vlog_special      timeprecision timeunit
syn keyword vlog_special      design liblist instance use cell incdir include

syn keyword vlog_conditional  if else case endcase casex casez
syn keyword vlog_conditional  inside unique unique0 priority
syn keyword vlog_conditional  generate endgenerate
syn keyword vlog_conditional  randcase
syn keyword vlog_repeat       forever repeat while for do foreach
syn keyword vlog_label        return continue break default
syn keyword vlog_label        begin end

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
syn keyword vlog_keyword      null this super std
syn keyword vlog_keyword      wait wait_order bind

syn keyword vlog_control      fork join join_any join_none forkjoin

syn match   vlog_function     "\$\=\(\s\+\.\)\@<!\<\w\+\ze("

" a bunch of "deprecated" keywords. e.g. defparam is pretty much considered
" evil in modern code. However, one might encounter it in library code or
" legacy code
syn keyword vlog_discouraged  defparam macromodule var

syn region  vlog_string start=+"+ skip=+\\"+ end=+"+ contains=vlog_escape,@Spell
syn match   vlog_escape +\\[nt"\\]+ contained
syn match   vlog_escape "\\\o\o\=\o\=" contained

syn case ignore
syn keyword vlog_todo         contained TODO FIXME XXX
syn case match
syn match   vlog_comment      "//.*" contains=vlog_todo,@Spell,vlog_bad_newline
syn region  vlog_comment      start="/\*" end="\*/" contains=vlog_todo,@Spell keepend

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

syn keyword vlog_assert        assert assume restrict expect cover
syn keyword vlog_keyword       accept_on reject_on
syn keyword vlog_keyword       sync_accept_on sync_reject_on
syn keyword vlog_keyword       eventually nexttime until until_with
syn keyword vlog_keyword       s_eventually s_nexttime s_until s_until_with
syn keyword vlog_keyword       s_always
syn keyword vlog_keyword       intersect first_match throughout within
syn keyword vlog_keyword       triggered matched iff disable
syn keyword vlog_keyword       property endproperty
syn keyword vlog_keyword       coverpoint bins illegal_bins ignore_bins illegal
syn keyword vlog_keyword       wildcard binsof
syn keyword vlog_structure     property endproperty

syn keyword vlog_modifier      rand randc
syn keyword vlog_statement     randomize constraint
syn keyword vlog_keyword       with solve before cross dist

syn keyword vlog_structure     sequence endsequence randsequence
syn keyword vlog_structure     covergroup endgroup
syn keyword vlog_keyword       untyped

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
hi default link vlog_typedef      Typedef

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

let b:current_syntax = "verilog_systemverilog"

" Restore cpoptions
let &cpoptions=oldcpo
