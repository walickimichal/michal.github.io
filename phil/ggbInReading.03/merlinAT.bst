%%
%% This is file `merlinAT.bst',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% merlin.mbs  (with options: `,ay,vonx,ed-au,nmdash,nmft,nmft-sc,nmfted,nmand-rm,yr-com,xmth,tit-it,atit-u,trtit-b,vnum-sp,volp-com,jwdpg,jwdvol,num-xser,edpar,blk-com,in-x,pp,abr,xedn,xand,etal-it')
%% ----------------------------------------
%% *** AuthorYear ***
%% 
%% Copyright 1994-1999 Patrick W Daly
 % ===============================================================
 % IMPORTANT NOTICE:
 % This bibliographic style (bst) file has been generated from one or
 % more master bibliographic style (mbs) files, listed above.
 %
 % This generated file can be redistributed and/or modified under the terms
 % of the LaTeX Project Public License Distributed from CTAN
 % archives in directory macros/latex/base/lppl.txt; either
 % version 1 of the License, or any later version.
 % ===============================================================
 % Name and version information of the main mbs file:
 % \ProvidesFile{merlin.mbs}[1999/05/28 3.89 (PWD)]
 %   For use with BibTeX version 0.99a or later
 %-------------------------------------------------------------------
 % This bibliography style file is intended for texts in ENGLISH
 % This is an author-year citation style bibliography. As such, it is
 % non-standard LaTeX, and requires a special package file to function properly.
 % Such a package is    natbib.sty   by Patrick W. Daly
 % The form of the \bibitem entries is
 %   \bibitem[Jones et al.(1990)]{key}...
 % The essential feature is that the label (the part in brackets) consists
 % of the author names, as they should appear in the citation, with the year
 % in parentheses following. There must be no space before the opening
 % parenthesis!
 % In natbib.sty, it is possible to define the type of enclosures that is
 % really wanted (brackets or parentheses), but in either case, there must
 % be parentheses in the label.
 % The \cite command functions as follows:
 %   \citet{key} ==>>                Jones et al. (1990)
 %   \citep{key} ==>>                (Jones et al., 1990)
 %   \citep[chap. 2]{key} ==>>       (Jones et al., 1990, chap. 2)
 %   \citep[e.g.][]{key} ==>>        (e.g. Jones et al., 1990)
 %   \citep[e.g.][p. 32]{key} ==>>   (e.g. Jones et al., p. 32)
 %   \citeauthor{key} ==>>           Jones et al.
 %   \citeyear{key} ==>>             1990
 %!! \citeauthor*{key}   -->         Jack Jones, Title
 %---------------------------------------------------------------------
%%
%% my additions/changes
 %
 %   \citeauthor*{key} ==>>           Andrew Jones, Emphasized Title
 %      if 1 editor    ==>>           A. Jones, ed., Emphasized Title
 %         2 editors   ==>>           A. Jones and J. Adams, ed., Emphasized Title
 %        >2 editors   ==>>           A. Jones et al., ed., Emphasized Title 
 
ENTRY
  { address
    author
    booktitle
    chapter
    edition
    editor
    howpublished
    institution
    journal
    key
    month
    note
    number
    organization
    pages
    publisher
    school
    series
    shortt
    title
    type
    volume
    year
  }
  {}
  { label extra.label sort.label short.list }

INTEGERS { output.state before.all mid.sentence after.sentence after.block }

FUNCTION {init.state.consts}
{ #0 'before.all :=
  #1 'mid.sentence :=
  #2 'after.sentence :=
  #3 'after.block :=
}

STRINGS { s t }

FUNCTION {output.nonnull}
{ 's :=
  output.state mid.sentence =
    { ", " * write$ }
    { output.state after.block =
        { add.period$  write$
          newline$
          "\newblock " write$
        }
        { output.state before.all =
            'write$
            { add.period$ " " * write$ }
          if$
        }
      if$
      mid.sentence 'output.state :=
    }
  if$
  s
}

FUNCTION {output}
{ duplicate$ empty$
    'pop$
    'output.nonnull
  if$
}

FUNCTION {output.check}
{ 't :=
  duplicate$ empty$
    { pop$ } %"empty " t * " in " * cite$ * warning$ }
    'output.nonnull
  if$
}

FUNCTION {fin.entry} % this is the ending of every entry in Bibliography
{ add.period$
  write$
  newline$
}

FUNCTION {new.block}
{ output.state before.all =
    'skip$
    { after.block 'output.state := }
  if$
}

FUNCTION {new.sentence}
{ output.state after.block =
    'skip$
    { output.state before.all =
        'skip$
        { after.sentence 'output.state := }
      if$
    }
  if$
}

FUNCTION {add.blank}
{  " " * before.all 'output.state :=
}

FUNCTION {date.block}
{
  skip$
}

FUNCTION {not}
{   { #0 }
    { #1 }
  if$
}

FUNCTION {and}
{   'skip$
    { pop$ #0 }
  if$
}

FUNCTION {or}
{   { pop$ #1 }
    'skip$
  if$
}

FUNCTION {new.block.checkb}
{ empty$
  swap$ empty$
  and
    'skip$
    'new.block
  if$
}

FUNCTION {field.or.null}
{ duplicate$ empty$
    { pop$ "" }
    'skip$
  if$
}

FUNCTION {emphasize}
{ duplicate$ empty$
    { pop$ "" }
    { "{\em " swap$ * "\/}" * }
  if$
}

FUNCTION {scaps}
{ duplicate$ empty$
    { pop$ "" }
    { "{\sc " swap$ * "}" * }
  if$
}

FUNCTION {bib.name.font}
{ scaps }

FUNCTION {bib.fname.font}
{ bib.name.font }

FUNCTION {capitalize}
{ "u" change.case$ "t" change.case$ }

FUNCTION {space.word}
{ " " swap$ * " " * }

 % Here are the language-specific definitions for explicit words.
 % Each function has a name bbl.xxx where xxx is the English word.
 % The language selected here is ENGLISH
FUNCTION {bbl.and}
{ "and"}

FUNCTION {bbl.etal}
{ "et~al." }

FUNCTION {bbl.editors}
{ "editors" }

FUNCTION {bbl.editor}
{ "editor" }

FUNCTION {bbl.edby}
{ "edited by" }

FUNCTION {bbl.edition}
%{ "edn." }
{ "" }

FUNCTION {bbl.volume}
{ "vol." }

FUNCTION {bbl.of}
{ "of" }

FUNCTION {bbl.number}
{ "no." }

FUNCTION {bbl.nr}
{ "no." }

FUNCTION {bbl.in}
{ "in" }

FUNCTION {bbl.pages}
{ "pp." }

FUNCTION {bbl.page}
{ "p." }

FUNCTION {bbl.chapter}
{ "chap." }

FUNCTION {bbl.techrep}
{ "Tech. Rep." }

FUNCTION {bbl.mthesis}
{ "Master's thesis" }

FUNCTION {bbl.phdthesis}
{ "Ph.D. thesis" }

MACRO {jan} {"Jan."}

MACRO {feb} {"Feb."}

MACRO {mar} {"Mar."}

MACRO {apr} {"Apr."}

MACRO {may} {"May"}

MACRO {jun} {"Jun."}

MACRO {jul} {"Jul."}

MACRO {aug} {"Aug."}

MACRO {sep} {"Sep."}

MACRO {oct} {"Oct."}

MACRO {nov} {"Nov."}

MACRO {dec} {"Dec."}


INTEGERS { nametot namesleft numnames }

FUNCTION {format.names}
{ 's :=
  "" 't :=
  #1 'nametot :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { s nametot
%      "{ff~}{vv~}{ll}{, jj}" format.name$
      "{vv~}{ll}{, ff}" format.name$
    bib.name.font
    't :=
      nametot #1 >
        {
          namesleft #1 >
%            { ", " * t * }
            { " and " * t * }
            {
              "," *
              s nametot "{ll}" format.name$ duplicate$ "others" =
                { 't := }
                { pop$ }
              if$
              t "others" =
                {
                  " " * bbl.etal emphasize *
                }
                { " and " * t * }
              if$
            }
          if$
        }
        't
      if$
      nametot #1 + 'nametot :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {format.names.ed}
{ format.names }

FUNCTION {format.key}
{ empty$
    { key field.or.null }
    { "" }
  if$
}

FUNCTION {format.authors}
{ author empty$
    { "" }
    { author format.names }
  if$
}

FUNCTION {format.editors}
{ editor empty$
    { "" }
    { editor format.names
      " (" *
      editor num.names$ #1 >
        'bbl.editors
        'bbl.editor
      if$
      * ")" *
    }
  if$
}

FUNCTION {format.in.editors}
{ editor empty$
    { "" }
    { editor format.names.ed
      editor num.names$ #1 >
        { " (" * bbl.editors * ")" * }
        { " (" * bbl.editor * ")" * }
      if$
    }
  if$
}

FUNCTION {format.note}
{
 note empty$
    { "" }
    { note #1 #1 substring$
      duplicate$
      "{" =
        'skip$
        { output.state mid.sentence =
           { "l" }
           { "l" } %{ "u" }
          if$
          change.case$
	   output.state mid.sentence =
           { "" *}
           { " " swap$ *} 
          if$
         
        }
      if$
%      " [" swap$ * %to put [ before the first char. of the note which got extracted
%      note #2 global.max$ substring$ * "]" *
      note #2 global.max$ substring$ *
    }
  if$
}

FUNCTION {format.title}
{ title empty$
    { "" }
    { %"``" title * "''" *
      title emphasize
    }
  if$
}
FUNCTION {format.title.quote}
{ title empty$
    { "" }
    { "``" title * "''" * emphasize
    }
  if$
}

FUNCTION {format.booktitle}
{ booktitle empty$
    { "" }
    { %"``" title * "''" *
      booktitle emphasize
    }
  if$
}

FUNCTION {output.bibitem}
{ newline$
  "\bibitem[" write$
  label write$
  ")]{" write$
  cite$ write$
  "}" write$
  newline$
  ""
  before.all 'output.state :=
}

FUNCTION {n.dashify} %not used anymore....
{
  't :=
  ""
    { t empty$ not }
    { t #1 #1 substring$ "-" =
        { t #1 #2 substring$ "----" = not
            { "----" *
              t #2 global.max$ substring$ 't :=
            }
            {   { t #1 #1 substring$ "-" = }
                { "-" *
                  t #2 global.max$ substring$ 't :=
                }
              while$
            }
          if$
        }
        { t #1 #1 substring$ *
          t #2 global.max$ substring$ 't :=
        }
      if$
    }
  while$
}

FUNCTION {word.in}
{ "" }

FUNCTION {format.date}
{ year duplicate$ empty$
    { %"empty year in " cite$ * "; ok" * warning$
       pop$ "" }
    {  ", " swap$ * }
  if$
  before.all 'output.state :=
}
% { year duplicate$ empty$
%     { "empty year in " cite$ * "; set to ????" * warning$
%        pop$ "????" }
%     'skip$
%   if$
%   extra.label *
%   before.all 'output.state :=
%   ", " swap$ *
%}

FUNCTION {format.btitle}
{ title emphasize
}

FUNCTION {tie.or.space.connect}
{ duplicate$ text.length$ #3 <
    { "~" }
    { " " }
  if$
  swap$ * *
}

FUNCTION {either.or.check}
{ empty$
    'pop$
    { "can't use both " swap$ * " fields in " * cite$ * warning$ }
  if$
}

FUNCTION {format.bvolume}
{ volume empty$
    { "" }
    { bbl.volume volume tie.or.space.connect
      series empty$
        'skip$
        { bbl.of space.word * series emphasize * }
      if$
      "volume and number" number either.or.check
    }
  if$
}

FUNCTION {format.number.series}
{ volume empty$
    { number empty$
        { series field.or.null }
        { series empty$
            { number }
        { output.state mid.sentence =
            { bbl.number }
            { bbl.number capitalize }
          if$
          number tie.or.space.connect
          bbl.in space.word * series *
        }
      if$
    }
      if$
    }
    { "" }
  if$
}


FUNCTION {format.edition}
{ edition empty$
    { "" }
    { output.state mid.sentence =
        { edition "l" change.case$ " " * bbl.edition * }
        { edition "t" change.case$ " " * bbl.edition * }
      if$
    }
  if$
}

INTEGERS { multiresult }

FUNCTION {multi.page.check}
{ 't :=
  #0 'multiresult :=
    { multiresult not
      t empty$ not
      and
    }
    { t #1 #1 substring$
      duplicate$ "-" =
      swap$ duplicate$ "," =
      swap$ "+" =
      or or
        { #1 'multiresult := }
        { t #2 global.max$ substring$ 't := }
      if$
    }
  while$
  multiresult
}

FUNCTION {format.pages}
{ pages empty$
    { "" }
    { pages multi.page.check
%        { bbl.pages pages n.dashify tie.or.space.connect }
        { bbl.pages pages tie.or.space.connect }
        { bbl.page pages tie.or.space.connect }
      if$
    }
  if$
}

FUNCTION {format.journal.pages}
{ pages empty$
    'skip$
    { duplicate$ empty$
        { pop$ format.pages }
        {
          ", " *
          pages multi.page.check
           { bbl.pages }
           { bbl.page }
          if$
          "~" * *
%          pages n.dashify *
          pages * % n.dashify *
        }
      if$
    }
  if$
}

FUNCTION {format.vol.num.pages}
{ volume field.or.null
  volume empty$
    'skip$
    { bbl.volume "~" * swap$ * }
  if$
  number empty$
    'skip$
    {
      "~(" number * ")" * *
      volume empty$
        { "there's a number but no volume in " cite$ * warning$ }
        'skip$
      if$
    }
  if$
  format.journal.pages
}

FUNCTION {format.chapter.pages}
{ chapter empty$
    'format.pages
    { type empty$
        { bbl.chapter }
        { type "l" change.case$ }
      if$
      chapter tie.or.space.connect
      pages empty$
        'skip$
        { ", " * format.pages * }
      if$
    }
  if$
}

FUNCTION {format.in.ed.booktitle}
{ booktitle empty$
    { "" }
    { editor empty$
%        { word.in booktitle emphasize * }
        { " in " booktitle emphasize * }
%        { word.in format.in.editors * ", " *
        { " in " format.in.editors * ", " *
          booktitle emphasize * }
      if$
    }
  if$
}

FUNCTION {format.thesis.type}
{ type empty$
    'skip$
    { pop$
      type "t" change.case$
    }
  if$
}

FUNCTION {format.tr.number}
{ type empty$
    { bbl.techrep }
    'type
  if$
  number empty$
    { "t" change.case$ }
    { number tie.or.space.connect }
  if$
}

FUNCTION {format.article.crossref}
{
%  word.in
%  " \citeauthor*{" *  crossref * "}" *
  " in "
  "  \citeauthor*{" *  crossref * "}" *  
}

FUNCTION {format.book.crossref}
{ volume empty$
    { %"empty volume in " cite$ * "'s crossref of " * crossref * warning$
      word.in
    }
    { bbl.volume volume tie.or.space.connect
      bbl.of space.word *
    }
  if$
  " in \citeauthor*{" * crossref * "}" *
}

FUNCTION {format.incoll.inproc.crossref}
{
%  word.in
  " in "
  " \citeauthor*{" * crossref * "}" *
}

FUNCTION {format.org.or.pub}
{ 't :=
  ""
  address empty$ t empty$ and
    'skip$
    {
      t empty$
        { address empty$
          'skip$
          { address * }
          if$
        }
        { t *
          address empty$
            'skip$
            { ", " * address * }
          if$
        }
      if$
    }
  if$
}

FUNCTION {format.publisher.address}
{ publisher empty$
    { %"empty publisher in " cite$ * warning$
      ""
    }
    { publisher }
  if$
  format.org.or.pub
}

FUNCTION {format.organization.address}
{ organization empty$
    { "" }
    { organization }
  if$
  format.org.or.pub
}

STRINGS {oldname}

FUNCTION {name.or.dash}
{ 's :=
   oldname empty$
     { s 'oldname := s }
     { s oldname =
         { "---" }
         { s 'oldname := s }
       if$
     }
   if$
}

FUNCTION {article}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  name.or.dash
  format.title.quote "title" output.check
  crossref missing$
    { journal
      emphasize
      "journal" output.check
      format.vol.num.pages output
      format.date "year" output.check
    }
    { format.article.crossref output.nonnull
      format.pages output
    }
  if$
  format.note output
  fin.entry
}

FUNCTION {book}
{ output.bibitem
  author empty$
    { format.editors "author and editor" output.check
      editor format.key output
      name.or.dash
    }
    { format.authors output.nonnull
      name.or.dash
      crossref missing$
        { "author and editor" editor either.or.check }
        'skip$
      if$
    }
  if$
%  format.btitle "title" output.check
  format.title "title" output.check
  booktitle missing$
    {}
    { format.booktitle "booktitle" output.check }
  if$
  crossref missing$
    { format.bvolume output
      format.number.series output
      format.publisher.address output
    }
    {
      format.book.crossref output.nonnull
    }
  if$
  format.edition output
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {booklet}
{ output.bibitem
  format.authors output
  author format.key output
  name.or.dash
  format.title "title" output.check
  howpublished output
  address output
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {inbook}
{ output.bibitem
  author empty$
    { format.editors "author and editor" output.check
      editor format.key output
      name.or.dash
    }
    { format.authors output.nonnull
      name.or.dash
      crossref missing$
        { "author and editor" editor either.or.check }
        'skip$
      if$
    }
  if$
  format.btitle "title" output.check
  crossref missing$
    {
      format.bvolume output
      format.chapter.pages "chapter and pages" output.check
      format.number.series output
      format.publisher.address output
    }
    {
      format.chapter.pages "chapter and pages" output.check
      format.book.crossref output.nonnull
    }
  if$
  format.edition output
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {incollection}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  name.or.dash
  format.title "title" output.check
  crossref missing$
    { format.in.ed.booktitle "booktitle" output.check
      format.bvolume output
      format.number.series output
      format.chapter.pages output
      format.publisher.address output
      format.edition output
      format.date "year" output.check
    }
    { format.incoll.inproc.crossref output.nonnull
      format.bvolume output
      format.chapter.pages output
    }
  if$
  format.note output
  fin.entry
}

FUNCTION {inproceedings}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  name.or.dash
  format.title "title" output.check
  crossref missing$
    { format.in.ed.booktitle "booktitle" output.check
      format.bvolume output
      format.number.series output
      format.pages output
      publisher empty$
        { format.organization.address output }
        { organization output
          format.publisher.address output
        }
      if$
      format.date "year" output.check
    }
    { format.incoll.inproc.crossref output.nonnull
      format.pages output
    }
  if$
  format.note output
  fin.entry
}

FUNCTION {conference} { inproceedings }

FUNCTION {manual}
{ output.bibitem
  format.authors output
  author format.key output
  name.or.dash
  format.btitle "title" output.check
  organization output
  address output
  format.edition output
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {mastersthesis}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  name.or.dash
  format.btitle "title" output.check
  bbl.mthesis format.thesis.type output.nonnull
  school "school" output.check
  address output
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {misc}
{ output.bibitem
  format.authors output
  author format.key output
  name.or.dash
  format.title output
  howpublished output
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {phdthesis}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  name.or.dash
  format.btitle "title" output.check
  bbl.phdthesis format.thesis.type output.nonnull
  school "school" output.check
  address output
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {proceedings}
{ output.bibitem
  format.editors output
  editor format.key output
  name.or.dash
  format.btitle "title" output.check
  format.bvolume output
  format.number.series output
  publisher empty$
    { format.organization.address output }
    { organization output
      format.publisher.address output
    }
  if$
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {techreport}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  name.or.dash
  format.btitle "title" output.check
  format.tr.number output.nonnull
  institution "institution" output.check
  address output
  format.date "year" output.check
  format.note output
  fin.entry
}

FUNCTION {unpublished}
{ output.bibitem
  format.authors "author" output.check
  author format.key output
  name.or.dash
  format.title "title" output.check
  format.date "year" output.check
  format.note "note" output.check
  fin.entry
}

FUNCTION {default.type} { misc }

READ

FUNCTION {sortify}
{ purify$
  "l" change.case$
}

INTEGERS { len }

FUNCTION {chop.word}
{ 's :=
  'len :=
  s #1 len substring$ =
    { s len #1 + global.max$ substring$ }
    's
  if$
}

FUNCTION {format.lab.names}
{ 's :=
  "" 't :=
  s #1 "{ff}" format.name$ "\NIX" =  %check if \NIX is there
  { s #1 "{}{vv~}{ll}" format.name$ } % and then ignore \NIX in label
%  s #1 "{ff~}{vv~}{ll}" format.name$
  { s #1 "{f.~}{vv~}{ll}" format.name$ } %: would turn \NIX into N.~
  if$
  s num.names$ duplicate$
  #2 >
    { pop$
      " " * bbl.etal emphasize *
    }
    { #2 <
        'skip$
%        { s #2 "{ff~}{vv }{ll}{ jj}" format.name$ "others" =
        { s #2 "{f.~}{vv }{ll}{ jj}" format.name$ "others" =
            {
              " " * bbl.etal emphasize *
            }
%            { ", " * s #2 "{ff~}{vv~}{ll}{ jj}" format.name$
            { ", " * s #2 "{f.~}{vv~}{ll}{ jj}" format.name$	    
%            { bbl.and space.word * s #2 "{ff}{vv~}{ll}{ jj}" format.name$	    
              * }
          if$
        }
      if$
    }
  if$
%  format.title %emphasize 
%  *
}

FUNCTION {author.key.label}
{ author empty$
    { key empty$
        { cite$ #1 #3 substring$ }
        'key
      if$
    }
    { author format.lab.names }
  if$
}


FUNCTION {format.short.lab.names}
{ 's :=
  "" 't :=
  s #1 "{f.~}{vv~}{ll}" format.name$
  s num.names$ duplicate$
  #2 >
    { pop$
      " " * bbl.etal emphasize *
    }
    { #2 <
        'skip$
        { s #2 "{f. }{vv }{ll}{ jj}" format.name$ "others" =
            {
              " " * bbl.etal emphasize *
            }
%            { ", " * s #2 "{f.~}{vv~}{ll}{ jj}" format.name$
            { bbl.and space.word * s #2 "{f. }{vv~}{ll}{ jj}" format.name$	    
              * }
          if$
        }
      if$
    }
  if$
}

FUNCTION {format.lab.editors} % not used - smth. wrong with "(" ")"...
{ editor format.short.lab.names
    editor num.names$ #1 >
      { " (" * bbl.editors * ")" * }
      { " (" * bbl.editor * ")" * }
    if$
}

FUNCTION {format.lab.title} %to get back, replace with format.title
{ shortt missing$
  { title duplicate$ empty$  
      { pop$ "" }
      { emphasize } % #-1 #4 substring$ }
   if$
  }
  { shortt emphasize }
  if$
}


FUNCTION {author.editor.key.label}
{ author empty$
    { editor empty$
        { format.lab.title }
        { editor format.short.lab.names
	  editor num.names$ #1 >
	   {", eds., "}
	   {", ed., "}
	  if$
	  *
	  format.lab.title *
	}
%%% no work        { format.lab.editors ", " * format.title * }
     if$
    }
    { author format.lab.names ", " * format.lab.title * }
  if$
}

FUNCTION {editor.key.label}
{ editor empty$
    { key empty$
        { cite$ #1 #3 substring$ }
        'key
      if$
    }
    { editor format.lab.names }
  if$
}

FUNCTION {calc.short.authors}
{ type$ "book" =
  type$ "inbook" =
  or
  type$ "article" =
  or
  type$ "incollection" =
  or
    'author.editor.key.label
       { type$ "proceedings" =
           'editor.key.label
           'author.key.label
         if$
    }
  if$
  'short.list :=
}

STRINGS {oldlabel}

FUNCTION {label.or.ibid}
% great idea but does not work, for calc.label is called only once
% when formatting the bibliography, not when producing the output for
% the \cite-kommands in the text!
{  's :=
   oldlabel empty$
     { s 'oldlabel := s }
     { s oldlabel =
         { "Ibid."  }
         { s 'oldlabel := s }
       if$
     }
   if$
}

FUNCTION {calc.label}
{ calc.short.authors
  short.list
  "("
  *
   title duplicate$ empty$  
      { pop$ "" }
      { purify$} % #-1 #4 substring$ }
   if$
  *
  'label :=
}

FUNCTION {sort.format.names}
{ 's :=
  #1 'nametot :=
  ""
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { s nametot
      "{ll{ }}{  ff{ }}{  jj{ }}"
      format.name$ 't :=
      nametot #1 >
        {
          "   "  *
          namesleft #1 = t "others" = and
            { "zzzzz" * }
            { t sortify * }
          if$
        }
        { t sortify * }
      if$
      nametot #1 + 'nametot :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

FUNCTION {sort.format.title}
{ 't :=
  "A " #2
    "An " #3
      "The " #4 t chop.word
    chop.word
  chop.word
  sortify
  #1 global.max$ substring$
}

FUNCTION {author.sort}
{ author empty$
    { key empty$
        { "to sort, need author or key in " cite$ * warning$
          ""
        }
        { key sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.editor.sort}
{ author empty$
    { editor empty$
        { title empty$
            { "to sort, need author, editor, or title in " cite$ * warning$
              ""
            }
            { title sortify }
          if$
        }
        { editor sort.format.names }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {editor.sort}
{ editor empty$
    { key empty$
        { "to sort, need editor or key in " cite$ * warning$
          ""
        }
        { key sortify }
      if$
    }
    { editor sort.format.names }
  if$
}

FUNCTION {presort}
{ calc.label
  label sortify
  "    "
  *
  type$ "book" =
  type$ "inbook" =
  or
%  type$ "article" =
%  or
    'author.editor.sort
    { type$ "proceedings" =
        'editor.sort
        'author.sort
      if$
    }
  if$
  #1 entry.max$ substring$
  'sort.label :=
  sort.label
  *
  "    "
  *
  title field.or.null
  sort.format.title
  *
  #1 entry.max$ substring$
  'sort.key$ :=
}

ITERATE {presort}

SORT

STRINGS { last.label next.extra }

INTEGERS { last.extra.num number.label }

FUNCTION {initialize.extra.label.stuff}
{ #0 int.to.chr$ 'last.label :=
  "" 'next.extra :=
  #0 'last.extra.num :=
  #0 'number.label :=
}

FUNCTION {forward.pass}
{ last.label label =
    { last.extra.num #1 + 'last.extra.num :=
      last.extra.num int.to.chr$ 'extra.label :=
    }
    { "a" chr.to.int$ 'last.extra.num :=
      "" 'extra.label :=
      label 'last.label :=
    }
  if$
  number.label #1 + 'number.label :=
}

FUNCTION {reverse.pass}
{ next.extra "b" =
    { "a" 'extra.label := }
    'skip$
  if$
  extra.label 'next.extra :=
  extra.label
  duplicate$ empty$
    'skip$
    { "{\natexlab{" swap$ * "}}" * }
  if$
  'extra.label :=
  label extra.label * 'label :=
}

EXECUTE {initialize.extra.label.stuff}

ITERATE {forward.pass}

REVERSE {reverse.pass}

FUNCTION {bib.sort.order}
{ sort.label
  "    "
  *
  year field.or.null sortify
  *
  "    "
  *
  title field.or.null
  sort.format.title
  *
  #1 entry.max$ substring$
  'sort.key$ :=
}

ITERATE {bib.sort.order}

SORT

FUNCTION {begin.bib}
{ preamble$ empty$
    'skip$
    { preamble$ write$ newline$ }
  if$
  "\begin{thebibliography}{" number.label int.to.str$ * "}" *
  write$ newline$
  "\expandafter\ifx\csname natexlab\endcsname\relax\def\natexlab#1{#1}\fi"
  write$ newline$
}

EXECUTE {begin.bib}

EXECUTE {init.state.consts}

ITERATE {call.type$}

FUNCTION {end.bib}
{ newline$
  "\end{thebibliography}" write$ newline$
}

EXECUTE {end.bib}
%% End of customized bst file
%%
%% End of file `merlinAY.bst'.
