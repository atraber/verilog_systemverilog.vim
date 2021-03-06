" Language:     Verilog/SystemVerilog HDL
"
" Credits:
"   Originally created by
"       Chih-Tsun Huang <cthuang@larc.ee.nthu.edu.tw>
"   http://larc.ee.nthu.edu.tw/~cthuang/vim/indent/verilog.vim
"   Suggestions for improvement, bug reports by
"     Leo Butlero <lbutler@brocade.com>
"   Last maintainer: Amit Sethi <amitrajsethi@yahoo.com>
"
" Buffer Variables:
"     b:verilog_indent_modules : indenting after the declaration
"        of module blocks
"     b:verilog_indent_width   : indenting width
"     b:verilog_indent_verbose : verbose to each indenting
"
" Revision Comments:
"     Amit Sethi - Wed Jun 28 18:20:44 IST 2006
"       Added SystemVerilog specific indentations
"     Amit Sethi - Thu Jul 27 12:09:48 IST 2006
"       Changed conflicting function name
"

" Only load this indent file when no other was loaded.
if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetVerilog_SystemVerilogIndent()
setlocal indentkeys=!^F,o,O,0),0},=begin,=end,=join,=endcase,=join_any,=join_none
setlocal indentkeys+==endmodule,=endfunction,=endtask,=endspecify
setlocal indentkeys+==endclass,=endpackage,=endsequence,=endclocking
setlocal indentkeys+==endinterface,=endgroup,=endprogram,=endproperty
setlocal indentkeys+==endgenerate
setlocal indentkeys+==`else,=`endif
setlocal indentkeys+==else

" Only define the function once.
if exists("*GetVerilog_SystemVerilogIndent")
  finish
endif

set cpo-=C

function s:prevnonblank(lnum)
  let lnum = prevnonblank(a:lnum)
  let line = getline(lnum)

  if exists("b:verilog_dont_indent_prep") &&
    \ line =~ '^\s*`\<\(ifdef\|ifndef\|else\|elsif\|endif\|define\|include\)\>'
    return s:prevnonblank(lnum-1)
  endif

  return lnum
endfunction

function GetVerilog_SystemVerilogIndent()

  if exists('b:verilog_indent_width')
    let offset = b:verilog_indent_width
  else
    let offset = &sw
  endif

  if exists('b:verilog_indent_prep')
    let offset_prep = b:verilog_indent_prep
  else
    let offset_prep = offset
  endif

  if exists('b:verilog_indent_modules')
    let indent_modules = offset
  else
    let indent_modules = &sw
  endif

  " Find a non-blank line above the current line.
  let lnum = s:prevnonblank(v:lnum - 1)

  " At the start of the file use zero indent.
  if lnum == 0
    return 0
  endif

  let lnum2 = s:prevnonblank(lnum - 1)
  let curr_line  = getline(v:lnum)
  let last_line  = getline(lnum)
  let last_line2 = getline(lnum2)
  let ind  = indent(lnum)
  let ind2 = indent(lnum - 1)
  let offset_comment1 = 1
  " Define the condition of an open statement
  "   Exclude the match of //, /* or */
  let vlog_openstat = '^\(\s*[/][/]\)\@!.*$\(\<or\>\|\([*/]\)\@<![*(,{><+-/%^&|!=?:]\([*/]\)\@!\)'
  " Matches or, *, /,
  " Define the condition when the statement ends with a one-line comment
  let vlog_comment = '\(//.*\|/\*.*\*/\s*\)'

  if exists('b:verilog_indent_verbose') && b:verilog_indent_verbose == 1
    let vverb = 1
  else
    let vverb = 0
  endif

  " Get new context line if it is fully commented out
  while last_line2 =~ '^\s*/\(/\|\*.*\*/\s*$\)'
    let lnum2 = s:prevnonblank(lnum2 - 1)
    let last_line2 = getline(lnum2)
  endwhile

  " Indent accoding to last line
  " End of multiple-line comment
  if last_line =~ '\*/\s*$' && last_line !~ '/\*.\{-}\*/'
    let ind = ind - offset_comment1
    if vverb
      echom "De-indent after a multiple-line comment:"
      echom last_line
    endif

  " Indent after if/else/for/case/always/initial/specify/fork blocks
  elseif last_line =~ '^\s*\(`\@<!\<\(if\|else\)\>\)' ||
    \ last_line =~ '^\s*\<\(for\|while\|do\|foreach\|randcase\)\>' ||
    \ last_line =~ '^\s*\(\<unique\>\)*\s*\<\(case\%[[zx]]\)\>' ||
    \ last_line =~ '^\s*\<\(always\|always_comb\|always_ff\|always_latch\)\>' ||
    \ last_line =~ '^\s*\<\(initial\|specify\|fork\|final\)\>' ||
    \ last_line =~ '^\s*\(\w\+\s*:\s*\)\?\<\(assert\|assume\|cover\)\>'
    if last_line !~ '\(;\|\<end\>\)\s*' . vlog_comment . '*$' ||
      \ last_line =~ '\(//\|/\*\).*\(;\|\<end\>\)\s*' . vlog_comment . '*$'
      if vverb
        echom "Indent after a block statement:"
        echom last_line
      endif

      let ind = ind + offset
    endif

  " indent after generate if | for, twice
  elseif last_line =~ '^\s*\(\<generate\>\)\s*\(`\@<!\<\(if\|for\)\>\)'
      if vverb
        echom "Indent after a generate if statement:"
        echom last_line
      endif

      let ind = ind + offset + offset

  " indent after standalone generate
  elseif last_line =~ '^\s*\(\<generate\>\)\s*'
      if vverb
        echom "Indent after a generate if statement:"
        echom last_line
      endif

      let ind = ind + offset

  " Indent after function/task/class/package/sequence/clocking/
  " interface/covergroup/property/program blocks
  elseif last_line =~ '^\s*\(\<\(static\|protected\|local\)\>\s\+\)\?\<\(function\|task\)\>' ||
    \ last_line =~ '^\s*\(\<virtual\>\s\+\)\?\<\(class\|package\)\>' ||
    \ last_line =~ '^\s*\<\(sequence\|clocking\|interface\)\>' ||
    \ last_line =~ '^\s*\(\w\+\s*:\)\=\s*\<covergroup\>' ||
    \ last_line =~ '^\s*\<\(property\|program\)\>'
    if last_line !~ '\<end\>\s*' . vlog_comment . '*$' ||
      \ last_line =~ '\(//\|/\*\).*\(;\|\<end\>\)\s*' . vlog_comment . '*$'
      let ind = ind + offset
      if vverb
        echom "Indent after function/task/class block statement:"
        echom last_line
      endif
    endif

  " Indent after module/function/task/specify/fork blocks
  elseif last_line =~ '^\s*\(\<extern\>\s*\)\=\<module\>'
    let ind = ind + indent_modules
    if vverb && indent_modules
      echom "Indent after module statement."
    endif
    if last_line =~ '[(,]\s*' . vlog_comment . '*$' &&
      \ last_line !~ '\(//\|/\*\).*[(,]\s*' . vlog_comment . '*$'
      let ind = ind + offset
      if vverb
        echom "Indent after a multiple-line module statement:"
        echom last_line
      endif
    endif

  " Indent after a 'begin' statement
  elseif last_line =~ '\(\<begin\>\)\(\s*:\s*\w\+\)*\s*' . vlog_comment . '*$' &&
    \ last_line !~ '\(//\|/\*\).*\(\<begin\>\)' &&
    \ ( last_line2 !~ vlog_openstat . '\s*' . vlog_comment . '*$' ||
    \ last_line2 =~ '^\s*[^=!]\+\s*:\s*' . vlog_comment . '*$' )
    let ind = ind + offset
    if vverb
      echom "Indent after begin statement:"
      echom last_line
    endif

  " Indent after a '{' or a '('
  elseif last_line =~ '[{(]' . vlog_comment . '*$' &&
    \ last_line !~ '\(//\|/\*\).*[{(]' &&
    \ ( last_line2 !~ vlog_openstat . '\s*' . vlog_comment . '*$' ||
    \ last_line2 =~ '^\s*[^=!]\+\s*:\s*' . vlog_comment . '*$' )
    let ind = ind + offset
    if vverb
      echom "Indent after begin statement:"
      echom last_line
    endif

  " De-indent for the end of one-line block
  " Only de-indents if last line was an end of statement that ended with ;
  " or if it starts with a `define call, which might not require the ; end
  elseif (
    \ last_line =~ ';\s*' . vlog_comment . '*$' ||
    \ last_line =~ '^\s*`\k\+'
    \ ) &&
    \ last_line2 =~ '\<\(`\@<!if\|`\@<!if\|else\|for\|while\|always\|initial\|do\|foreach\|final\)\>\(\s*(.*)\)\?\s*' . vlog_comment . '*$' &&
    \ last_line2 !~ '\(//\|/\*\).*\<\(`\@<!if\|`\@<!if\|else\|for\|while\|always\|initial\|do\|foreach\|final\)\>' &&
    \ ( last_line2 !~ '\<\(begin\|assert\)\>' ||
    \   last_line2 =~ '\(//\|/\*\).*\<\(begin\|assert\)\>' )
    let ind = ind - offset
    if vverb
      echom "De-indent after the end of one-line statement:"
      echom last_line2
    endif

    " Multiple-line statement (including case statement)
    " Open statement
    "   Indent the first open line
    elseif  last_line =~ vlog_openstat . '\s*' . vlog_comment . '*$' &&
      \ last_line !~ '\(//\|/\*\).*' . vlog_openstat . '\s*$' &&
      \ last_line2 !~ vlog_openstat . '\s*' . vlog_comment . '*$'
      let ind = ind + offset
      if vverb
        echom "Indent after an open statement:"
        echom last_line
      endif

    " Close statement
    "   De-indent for an optional close parenthesis and a semicolon, and only
    "   if there exists precedent non-whitespace char
    "   Also de-indents a close bracket when preceded by a semicolon, but only
    "   if it is not commented out or alone in a line. "with" statements are
    "   also ignored.
    elseif last_line =~ ')\s*;\s*' . vlog_comment . '*$' &&
      \ last_line !~ '\(//\|/\*\).*\S)*\s*;\s*' . vlog_comment . '*$' &&
      \ ( last_line2 =~ vlog_openstat . '\s*' . vlog_comment . '*$' &&
      \ last_line2 !~ ';\s*//.*$') &&
      \ last_line2 !~ '^\s*' . vlog_comment . '$' ||
      \ last_line =~ ';\s*}' && last_line !~ vlog_comment . '}' && last_line !~ '^\s*}' && last_line !~ '\<with\s*{'
      let ind = ind - offset
      if vverb
        echom "De-indent after a close statement:"
        echom last_line
      endif

  " `ifdef , `ifndef , `elsif , or `else
  elseif last_line =~ '^\s*`\<\(ifdef\|ifndef\|elsif\|else\)\>'
    let ind = ind + offset
    if vverb
      echom "Indent after a `ifdef , `ifndef , `elsif or `else statement."
      echom last_line
    endif

  endif

  " Re-indent current line

  " De-indent on the end of the block
  " join/end/endcase/endfunction/endtask/endspecify
  if curr_line =~ '^\s*\<\(join\|join_any\|join_none\|end\|endcase\)\>' ||
      \ curr_line =~ '^\s*\<\(endfunction\|endtask\|endspecify\|endclass\)\>' ||
      \ curr_line =~ '^\s*\<\(endpackage\|endsequence\|endclocking\|endinterface\)\>' ||
      \ curr_line =~ '^\s*\<\(endgroup\|endproperty\|endprogram\)\>' ||
      \ curr_line =~ '^\s*\<\(endgenerate\)\>' ||
      \ curr_line =~ '^\s*}' ||
      \ curr_line =~ '^\s*)\s*'
    let ind = ind - offset
    if vverb
      echom "De-indent the end of a block:"
      echom curr_line
    endif
  elseif curr_line =~ '^\s*\<endmodule\>'
    if exists("g:verilog_dont_deindent_eos")
      let ind = ind - offset
    else
      let ind = ind - indent_modules - offset
    endif
    if vverb
      echom "De-indent the end of a module:"
      echom curr_line
    endif

  " De-indent else of assert
  elseif curr_line =~ '\<else\>' &&
    \ last_line =~ '^\s*\(\w\+\s*:\s*\)\?\<\(assert\)\>\s*(.*)' . vlog_comment . '*$'
    let ind = ind - offset
    if vverb
      echom "De-indent else of assert"
      echom curr_line
    endif

    " De-indent else after else
  elseif curr_line =~ '^\s*\<else\>' &&
    \ last_line2 =~ '^\s*\<else\>'
    let ind = ind - offset
    if vverb
      echom "De-indent else after else"
      echom curr_line
    endif

  " De-indent on a stand-alone 'begin'
  elseif curr_line =~ '^\s*\<begin\>'
    if last_line !~ '^\s*\<\(fork\)\>' &&
      \ last_line !~ '^\s*\<\(function\|task\|specify\|module\|class\|package\)\>' &&
      \ last_line !~ '^\s*\<\(sequence\|clocking\|interface\|covergroup\)\>'  &&
      \ last_line !~ '^\s*\<\(property\|program\)\>' &&
      \ last_line !~ '^\s*\()*\s*;\|)\+\)\s*' . vlog_comment . '*$' && (
        \ last_line =~
        \ '\<\(`\@<!if\|`\@<!else\|for\|while\|case\%[[zx]]\|always\|always_comb\|always_ff\|always_latch\|initial\|do\|foreach\|randcase\|final\)\>' ||
        \ last_line =~ ')\s*' . vlog_comment . '*$' ||
        \ last_line =~ vlog_openstat . '\s*' . vlog_comment . '*$' )
      let ind = ind - offset
      if vverb
        echom "De-indent a stand alone begin statement:"
        echom last_line
      endif
    endif

  " De-indent at the end of multiple-line statement
  elseif !exists("g:verilog_dont_deindent_eos") && curr_line =~ '^\s*)' &&
    \ ( last_line =~ vlog_openstat . '\s*' . vlog_comment . '*$' ||
    \ last_line !~ vlog_openstat . '\s*' . vlog_comment . '*$' &&
    \ last_line2 =~ vlog_openstat . '\s*' . vlog_comment . '*$' )
    let ind = ind - offset
    if vverb
      echom "De-indent at the end of a multiple statement:"
      echom last_line
    endif

  " De-indent after the end of multiple-line statement
  elseif exists("g:verilog_dont_deindent_eos") && last_line =~ '^\s*)' "&&
    "\ last_line2 =~ vlog_openstat . '\s*' . vlog_comment . '*$'
    let ind = ind - offset
    if vverb
      echom "De-indent after the end of a multiple statement:"
      echom last_line
    endif

  " De-indent `else , `elsif , or `endif
  elseif !exists("b:verilog_dont_indent_prep") &&
    \ curr_line =~ '^\s*`\<\(else\|elsif\|endif\)\>'
    let ind = ind - offset
    if vverb
      echom "De-indent `else , `elsif , or `endif statement:"
      echom curr_line
    endif

  " Set indent to 0 for all preprocessor commands
  elseif exists("b:verilog_dont_indent_prep") &&
    \ curr_line =~ '^\s*`\<\(ifdef\|ifndef\|else\|elsif\|endif\|define\|include\)\>'
    let ind = 0
    if vverb
      echom "Preprocessor command found, set indent to 0"
      echom curr_line
    endif

  endif

  " Return the indention
  return ind
endfunction

" vim:sw=2
