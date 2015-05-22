------------------------------------------------------------------------------
--- This library provides pretty printing combinators.
--- The interface is that of
--- [Daan Leijen's library](<http://www.cs.uu.nl/~daan/download/pprint/pprint.html)
--- (`fill`, `fillBreak` and `indent` are missing) with a
--- [linear-time, bounded implementation](http://www.cs.kent.ac.uk/pubs/2006/2381/index.html)
---  by Olaf Chitil.
---
--- @author Sebastian Fischer, Björn Peemöller
--- @version January 2015
------------------------------------------------------------------------------

{-# OPTIONS_CYMAKE -X TypeClassExtensions #-}

module Pretty (

  -- pretty printer and document type
  pretty, Doc,

  -- basic document combinators
  empty, isEmpty, text, linesep, line, linebreak, group, softline, softbreak,

  -- alignment combinators
  nest, hang, align, indent,

  -- composition combinators
  combine, (<>), (<+>), (<$>), (<$+>), (</>), (<$$>), (<//>), ($$), ($+$),

  -- list combinators
  compose, hsep, hsepMap, vsep, vsepMap, fillSep, sep, hcat, hcatMap, vcat,
  vcatMap, fillCat, cat, punctuate, encloseSep, hEncloseSep, fillEncloseSep,
  fillEncloseSepSpaced, list, listSpaced, set, setSpaced, tupled, tupledSpaced,
  semiBraces, semiBracesSpaced,

  -- bracketing combinators
  enclose, squotes, dquotes, bquotes, parens,
  parensIf, angles, braces, brackets,

  -- fillers
  fill, fillBreak,

  -- primitve type documents
  char, string, int, float,

  -- character documents
  lparen, rparen, langle, rangle, lbrace, rbrace, lbracket, rbracket,
  squote, dquote, semi, colon, comma, space, dot, backslash, equals,
  arrow, doubleArrow, doubleColon, bar, at, tilde

  ) where

import Dequeue as Q

infixl 1 <>, <+>, <$>, </>, <$$>, <//>

--- The abstract data type Doc represents pretty documents.
data Doc = Doc (Tokens -> Tokens)

--- Extract the internal representation from a document.
deDoc :: Doc -> Tokens -> Tokens
deDoc (Doc d) = d

--- The empty document is, indeed, empty. Although empty has no content,
--- it does have a 'height' of 1 and behaves exactly like `(text "")`
--- (and is therefore not a unit of `<$>`).
--- @return an empty document
empty :: Doc
empty = text ""

--- Is the document empty?
isEmpty :: Doc -> Bool
isEmpty (Doc d) = isEmptyText (d Empty)
 where isEmptyText t = case t of Text s Empty -> null s
                                 _            -> False

--- The document `(text s)` contains the literal string `s`.
--- The string shouldn't contain any newline ('\n') characters.
--- If the string contains newline characters,
--- the function `string` should be used.
--- @param s - a string without newline (`'\n'`) characters
--- @return a document which contains the literal string
text :: String -> Doc
text s = Doc (Text s)

--- The document `(linesep s)` advances to the next line and indents
--- to the current nesting level. Document `(linesep s)`
--- behaves like `(text s)` if the line break is undone by group.
--- @param s - a string
--- @return a document which advances to the next line or behaves like `(text s)`
linesep :: String -> Doc
linesep = Doc . Line

--- The line document advances to the next line and indents to the current
--- nesting level. Document line behaves like `(text " ")` if the line break
--- is undone by group.
--- @return a document which advances to the next line or behaves
---         like `(text " ")`
line :: Doc
line = linesep " "

--- The linebreak document advances to the next line and indents to
--- the current nesting level. Document linebreak behaves like empty
--- if the line break is undone by group.
--- @return a document which advances to the next line or behaves like
---         `(text "")`
linebreak :: Doc
linebreak = linesep ""

--- The document softline behaves like `space` if the resulting output
--- fits the page, otherwise it behaves like `line`.<br><br>
--- `softline  = group line`
--- @return a document which behaves like `space` or `line`
softline :: Doc
softline = group line

--- The document softbreak behaves like `empty` if the resulting output
--- fits the page, otherwise it behaves like `line`.<br><br>
--- `softbreak  = group linebreak`
--- @return a document which behaves like `empty` or `line`
softbreak :: Doc
softbreak = group linebreak

--- The group combinator is used to specify alternative layouts.
--- The document `(group x)` undoes all line breaks in document `x`.
--- The resulting line is added to the current line if that fits the page.
--- Otherwise, the document x is rendered without any changes.
--- @param d - a document
--- @return document d without line breaks if that fits the page.
group :: Doc -> Doc
group d = Doc (Open . deDoc d . Close)

--- The document `(nest i d)` renders document `d` with the current
--- indentation level increased by `i` (See also `hang`,
--- `align` and `indent`).
---
---     nest 2 (text "hello" <$> text "world") <$> text "!"
---
--- outputs as:
---
---     hello
---       world
---     !
---
--- @param i - an integer which increases the indentation level
--- @param d - a document
--- @return document d with an indentation level increased by i
nest :: Int -> Doc -> Doc
nest i d = Doc (OpenNest (\ms@(m:_) _ _ -> (m + i) : ms) . deDoc d . CloseNest)

--- The hang combinator implements hanging indentation.
--- The document `(hang i d)` renders document `d` with a nesting level set
--- to the current column plus `i`. The following example uses hanging
--- indentation for some text:
---
---     test = hang 4
---              (fillSep
---                 (map text
---                      (words "the hang combinator indents these words !")))
---
--- Which lays out on a page with a width of 20 characters as:
---
---     the hang combinator
---         indents these
---         words !
---
--- The hang combinator is implemented as:
---
---     hang i x  = align (nest i x)
---
--- @param i - an integer which increases the indentation level
--- @param d - a document
--- @return document d with an indentation level set to the current column plus i
hang :: Int -> Doc -> Doc
hang i d = Doc (OpenNest (\ms r w -> (w - r + i) : ms) . deDoc d . CloseNest)

--- The document `(align d)` renders document `d with the nesting level
--- set to the current column. It is used for example to implement hang.
---
--- As an example, we will put a document right above another one,
--- regardless of the current nesting level:
---
---     x $$ y  = align (x <$> y)
---     test    = text "hi" <+> (text "nice" $$ text "world")
---
--- which will be layed out as:
---
---     hi nice
---        world
---
--- @param d - a document
--- @return document d with the nesting level set to the current column
align :: Doc -> Doc
align = hang 0


--- The document `(indent i d)` indents document `d` with `i` spaces.
---
---     test  = indent 4 (fillSep (map text
---             (words "the indent combinator indents these words !")))
---
--- Which lays out with a page width of 20 as:
---
---     the indent
---     combinator
---     indents these
---     words !
---
--- @param i - an integer which increases the indentation level
--- @param d - a document
--- @return document d with an indentation level set to the current column plus i
indent :: Int -> Doc -> Doc
indent i d = hang i (spaces i <> d)

--- The document `(combine x l r)` encloses document `x` between
--- documents `l` and `r` using `(<>)`.
---
---     combine x l r   = l <> x <> r
---
--- @param x - the middle document
--- @param l - the left document
--- @param r - the right document
--- @return concatenation of l, x and r
combine :: Doc -> Doc -> Doc -> Doc
combine s d1 d2 = enclose d1 d2 s

--- The document `(x <> y)` concatenates document `x` and document `y`.
--- It is an associative operation having empty as a left and right unit.
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y without seperator
(<>) :: Doc -> Doc -> Doc
d1 <> d2 = Doc (deDoc d1 . deDoc d2)

--- The document `(x <+> y)` concatenates document `x` and `y` with a
--- `space` in between.
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y with a `space` in between
(<+>) :: Doc -> Doc -> Doc
(<+>) = combine space

--- The document `(x <$> y)` concatenates document x and y with a
--- `line` in between.
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y with a `line` in between
(<$>) :: Doc -> Doc -> Doc
(<$>) = combine line

--- The document `(x <$+> y)` concatenates document x and y with a
--- blank line in between.
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y with a `line` in between
(<$+>) :: Doc -> Doc -> Doc
(<$+>) = combine (line <> line)

--- The document (x $$ y) concatenates documents x and y with a `line`
--- in between, just like `<$>`, but with identity empty.
--- Thus, the following equations hold:
---
---     d1    $$ empty == d1
---     empty $$ d2    == d2
---     d1    $$ d2    == d1 <$> d2 if neither d1 nor d2 are empty
---
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y with a `line` in between unless one
---         of the documents is empty
($$) :: Doc -> Doc -> Doc
($$) d1 d2 | isEmpty d1 = d2
           | isEmpty d2 = d1
           | otherwise  = d1 <$> d2

--- The document `(x $+$ y)` concatenates documents `x` and `y` with a
--- blank line in between, just like `<$+>`, but with identity empty.
--- Thus, the following equations hold:
---
---     d1    $+$ empty == d1
---     empty $+$ d2    == d2
---     d1    $+$ d2    == d1 <$+> d2 if neither d1 nor d2 are empty
---
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y with a blank line in between unless one
---         of the documents is empty
($+$) :: Doc -> Doc -> Doc
($+$) d1 d2 | isEmpty d1 = d2
            | isEmpty d2 = d1
            | otherwise  = d1 <$+> d2

--- The document `(x </> y)` concatenates document `x` and `y` with
--- a `softline` in between. This effectively puts `x` and `y` either
--- next to each other (with a `space` in between)
--- or underneath each other.
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y with a `softline` in between
(</>) :: Doc -> Doc -> Doc
(</>) = combine softline

--- The document `(x <$$> y)` concatenates document `x` and `y` with a
--- `linebreak` in between.
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y with a `linebreak` in between
(<$$>) :: Doc -> Doc -> Doc
(<$$>) = combine linebreak

--- The document `(x <//> y)` concatenates document `x` and `y` with a
--- `softbreak` in between. This effectively puts `x` and `y` either
--- right next to each other or underneath each other.
--- @param x - the first document
--- @param y - the second document
--- @return concatenation of x and y with a `softbreak` in between
(<//>) :: Doc -> Doc -> Doc
(<//>) = combine softbreak

--- The document (compose f xs) concatenates all documents xs with function f.
--- Function f should be like `(<+>)`, `(<$>)` and so on.
--- @param f - a combiner function
--- @param xs - a list of documents
--- @return concatenation of documents
compose :: (Doc -> Doc -> Doc) -> [Doc] -> Doc
--compose op = foldr op empty
compose _ []        = empty
compose op ds@(_:_) = foldr1 op ds -- no seperator at the end

--- The document (hsep xs) concatenates all documents xs
--- horizontally with `(<+>)`.
--- @param xs - a list of documents
--- @return horizontal concatenation of documents
hsep :: [Doc] -> Doc
hsep = compose (<+>)

--- The document (hsepMap f xs) generates a list of documents by
--- applying `f` to all list elements. Then it concatenates these
--- documents horizontally using `hsep`.
--- @param f  - a function to generate documents
--- @param xs - a list of arbitrary elements
--- @return horizontal concatenation of generated documents
hsepMap :: (a -> Doc) -> [a] -> Doc
hsepMap f = hsep . map f

--- The document `(vsep xs)` concatenates all documents `xs` vertically with
--- `(<$>)`. If a group undoes the line breaks inserted by `vsep`,
--- all documents are separated with a `space`.
---
---     someText = map text (words ("text to lay out"))
---     test     = text "some" <+> vsep someText
---
--- This is layed out as:
---
---     some text
---     to
---     lay
---     out
---
--- The `align` combinator can be used to align the documents
--- under their first element:
---
---     test     = text "some" <+> align (vsep someText)
---
--- This is printed as:
---
---     some text
---          to
---          lay
---          out
---
--- @param xs - a list of documents
--- @return vertical concatenation of documents
vsep :: [Doc] -> Doc
vsep = compose (<$>)

--- The document (vsepMap f xs) generates a list of documents by
--- applying `f` to all list elements. Then it concatenates these
--- documents vertically using `vsep`.
--- @param f  - a function to generate documents
--- @param xs - a list of arbitrary elements
--- @return vertical concatenation of generated documents
vsepMap :: (a -> Doc) -> [a] -> Doc
vsepMap f = vsep . map f

--- The document (fillSep xs) concatenates documents xs horizontally with
--- `(<+>)` as long as its fits the page, than inserts a
--- `line` and continues doing that for all documents in xs.<br><br>
--- `fillSep xs  = foldr (</>) empty xs`
--- @param xs - a list of documents
--- @return horizontal concatenation of documents
fillSep :: [Doc] -> Doc
fillSep = compose (</>)

--- The document (sep xs) concatenates all documents xs either horizontally
--- with `(<+>)`, if it fits the page, or vertically
--- with `(<$>)`.<br><br>
--- `sep xs  = group (vsep xs)`
--- @param xs - a list of documents
--- @return horizontal concatenation of documents, if it fits the page,
--- or vertical concatenation else
sep :: [Doc] -> Doc
sep = group . vsep

--- The document (hcat xs) concatenates all documents xs horizontally
--- with `(<>)`.
--- @param xs - a list of documents
--- @return horizontal concatenation of documents
hcat :: [Doc] -> Doc
hcat = compose (<>)

--- The document (hcatMap f xs) generates a list of documents by
--- applying `f` to all list elements. Then it concatenates these
--- documents horizontally using `hcat`.
--- @param f  - a function to generate documents
--- @param xs - a list of arbitrary elements
--- @return horizontal concatenation of generated documents
hcatMap :: (a -> Doc) -> [a] -> Doc
hcatMap f = hcat . map f

--- The document (vcat xs) concatenates all documents xs vertically
--- with `(<$$>)`. If a `group` undoes the line
--- breaks inserted by `vcat`, all documents are directly
--- concatenated.
--- @param xs - a list of documents
--- @return vertical concatenation of documents
vcat :: [Doc] -> Doc
vcat = compose (<$$>)

--- The document (vcatMap f xs) generates a list of documents by
--- applying `f` to all list elements. Then it concatenates these
--- documents vertically using `vcat`.
--- @param f  - a function to generate documents
--- @param xs - a list of arbitrary elements
--- @return vertical concatenation of generated documents
vcatMap :: (a -> Doc) -> [a] -> Doc
vcatMap f = vcat . map f

--- The document (fillCat xs) concatenates documents xs horizontally
--- with `(<>)` as long as its fits the page, than inserts
--- a `linebreak` and continues doing that for all documents in xs.
--- <br><br>
--- `fillCat xs  = foldr (<//>) empty xs`
--- @param xs - a list of documents
--- @return horizontal concatenation of documents
fillCat :: [Doc] -> Doc
fillCat = compose (<//>)

--- The document (cat xs) concatenates all documents xs either horizontally
--- with `(<>)`, if it fits the page, or vertically with
--- `(<$$>)`.<br><br>
--- `cat xs  = group (vcat xs)`
--- @param xs - a list of documents
--- @return horizontal concatenation of documents
cat :: [Doc] -> Doc
cat = group . vcat

--- `(punctuate p xs)` concatenates all documents `xs` with document `p` except
--- for the last document.
---
---     someText = map text ["words","in","a","tuple"]
---     test     = parens (align (cat (punctuate comma someText)))
---
--- This is layed out on a page width of 20 as:
---
---     (words,in,a,tuple)
---
--- But when the page width is 15, it is layed out as:
---
---     (words,
---      in,
---      a,
---      tuple)
---
--- (If you want put the commas in front of their elements instead of at the
--- end, you should use `tupled` or, in general,
--- `encloseSep`.)
--- @param p - a document as seperator
--- @param xs - a list of documents
--- @return concatenation of documents with p in between
punctuate :: Doc -> [Doc] -> [Doc]
punctuate d ds = go ds
 where
  go []           = []
  go [x]          = [x]
  go (x:xs@(_:_)) = (x <> d) : go xs

--- The document (encloseSep l r sep xs) concatenates the documents xs
--- seperated by sep and encloses the resulting document by l and r.<br>
--- The documents are rendered horizontally if that fits the page. Otherwise
--- they are aligned vertically. All seperators are put in front of the
--- elements.
---
--- For example, the combinator `list` can be defined with `encloseSep`:
---
---     list xs  = encloseSep lbracket rbracket comma xs
---     test     = text "list" <+> (list (map int [10,200,3000]))
---
--- Which is layed out with a page width of 20 as:
---
---     list [10,200,3000]
---
--- But when the page width is 15, it is layed out as:
---
---     list [10
---          ,200
---          ,3000]
---
--- @param l - left document
--- @param r - right document
--- @param sep - a document as seperator
--- @param xs - a list of documents
--- @return concatenation of l, xs (with p in between) and r
encloseSep :: Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSep l r _ [] = l <> r
encloseSep l r s (d:ds) = align (enclose l r (cat (d:map (s<>) ds)))

--- The document `(hEncloseSep l r sep xs)` concatenates the documents `xs`
--- seperated by `sep` and encloses the resulting document by `l` and `r`.
---
--- The documents are rendered horizontally.
--- @param l - left document
--- @param r - right document
--- @param sep - a document as seperator
--- @param xs - a list of documents
--- @return concatenation of l, xs (with p in between) and r
hEncloseSep :: Doc -> Doc -> Doc -> [Doc] -> Doc
hEncloseSep l r _ [] = l <> r
hEncloseSep l r s (d:ds) = align (enclose l r (hcat (d:map (s<>) ds)))

--- The document `(fillEncloseSep l r sep xs)` concatenates the documents `xs`
--- seperated by `sep` and encloses the resulting document by `l` and `r`.
---
--- The documents are rendered horizontally if that fits the page.
--- Otherwise they are aligned vertically.
--- All seperators are put in front of the elements.
--- @param l - left document
--- @param r - right document
--- @param sep - a document as seperator
--- @param xs - a list of documents
--- @return concatenation of l, xs (with p in between) and r
fillEncloseSep :: Doc -> Doc -> Doc -> [Doc] -> Doc
fillEncloseSep l r _ [] = l <> r
fillEncloseSep l r s (d:ds)
  = align (enclose l r (hcat (d:withSoftBreaks (map (s<>) ds))))
 where
  withSoftBreaks []  = []
  withSoftBreaks [x] = [group (linebreak <> x)]
  withSoftBreaks (x:xs@(_:_))
    = (group (linebreak <> (group (x <> linebreak))) : withSoftBreaks xs)

--- The document `(fillEncloseSepSpaced l r sep xs)` concatenates the documents
--- v seperated by `sep` and encloses the resulting document by `l` and `r`.
--- In addition, after each occurrence of `sep`, after `l`, and before `r`,
--- a `space` is inserted.
---
--- The documents are rendered horizontally if that fits the page.
--- Otherwise, they are aligned vertically.
--- All seperators are put in front of the elements.
--- @param l - left document
--- @param r - right document
--- @param sep - a document as seperator
--- @param xs - a list of documents
--- @return concatenation of l, xs (with p in between) and r
fillEncloseSepSpaced :: Doc -> Doc -> Doc -> [Doc] -> Doc
fillEncloseSepSpaced l r s =
  fillEncloseSep (l <> space) (space <> r) (s <> space)

--- The document (list xs) comma seperates the documents xs and encloses
--- them in square brackets. The documents are rendered horizontally if
--- that fits the page. Otherwise they are aligned vertically.
--- All comma seperators are put in front of the elements.
--- @param xs - a list of documents
--- @return comma seperated documents xs and enclosed
--- in square brackets
list :: [Doc] -> Doc
list = fillEncloseSep lbracket rbracket comma

--- Spaced version of `list`
listSpaced :: [Doc] -> Doc
listSpaced = fillEncloseSepSpaced lbracket rbracket comma

--- The document (set xs) comma seperates the documents xs and encloses
--- them in braces. The documents are rendered horizontally if
--- that fits the page. Otherwise they are aligned vertically.
--- All comma seperators are put in front of the elements.
--- @param xs - a list of documents
--- @return comma seperated documents xs and enclosed
--- in braces
set :: [Doc] -> Doc
set = fillEncloseSep lbrace rbrace comma

--- Spaced version of `set`
setSpaced :: [Doc] -> Doc
setSpaced = fillEncloseSepSpaced lbrace rbrace comma

--- The document (tupled xs) comma seperates the documents xs and encloses
--- them in parenthesis. The documents are rendered horizontally if that fits
--- the page. Otherwise they are aligned vertically.
--- All comma seperators are put in front of the elements.
--- @param xs - a list of documents
--- @return comma seperated documents xs and enclosed
--- in parenthesis
tupled :: [Doc] -> Doc
tupled = fillEncloseSep lparen rparen comma

--- Spaced version of `tupled`
tupledSpaced :: [Doc] -> Doc
tupledSpaced = fillEncloseSepSpaced lparen rparen comma

--- The document (semiBraces xs) seperates the documents xs with semi colons
--- and encloses them in braces. The documents are rendered horizontally
--- if that fits the page. Otherwise they are aligned vertically.
--- All semi colons are put in front of the elements.
--- @param xs - a list of documents
--- @return documents xs seperated with semi colons and enclosed
--- in braces
semiBraces :: [Doc] -> Doc
semiBraces = fillEncloseSep lbrace rbrace semi

--- Spaced version of `semiBraces`
semiBracesSpaced :: [Doc] -> Doc
semiBracesSpaced = fillEncloseSepSpaced lbrace rbrace semi

--- The document (enclose l r x) encloses document x between
--- documents l and r using `(<>)`.<br><br>
--- `enclose l r x   = l <> x <> r`
--- @param l - the left document
--- @param r - the right document
--- @param x - the middle document
--- @return concatenation of l, x and r
enclose :: Doc -> Doc -> Doc -> Doc
enclose l r d = l <> d <> r

--- Document (squotes x) encloses document x with single quotes `"'"`.
--- @param x - a document
--- @return document x enclosed by single quotes
squotes :: Doc -> Doc
squotes = enclose squote squote

--- Document (dquotes x) encloses document x with double quotes.
--- @param x - a document
--- @return document x enclosed by double quotes
dquotes :: Doc -> Doc
dquotes = enclose dquote dquote

--- Document (bquotes x) encloses document x with back quotes `"\`"`.
--- @param x - a document
--- @return document x enclosed by `\`` quotes
bquotes  :: Doc -> Doc
bquotes = enclose bquote bquote

--- Document (parens x) encloses document x in parenthesis,
--- `"("` and `")"`.
--- @param x - a document
--- @return document x enclosed in parenthesis
parens :: Doc -> Doc
parens = enclose lparen rparen

--- Document (parens x) encloses document x in parenthesis,`"("` and `")"`,
--- iff the condition is true.
--- @param x - a document
--- @return document x enclosed in parenthesis iff the condition is true
parensIf :: Bool -> Doc -> Doc
parensIf b s = if b then parens s else s

--- Document (angles x) encloses document x in angles,
--- `"<"` and `">"`.
--- @param x - a document
--- @return document x enclosed in angles
angles :: Doc -> Doc
angles = enclose langle rangle

--- Document (braces x) encloses document x in braces,
--- `"{"` and `"}"`.
--- @param x - a document
--- @return document x enclosed in braces
braces :: Doc -> Doc
braces = enclose lbrace rbrace

--- Document (brackets x) encloses document x in square brackets,
--- `"["` and `"]"`.
--- @param x - a document
--- @return document x enclosed in square brackets
brackets :: Doc -> Doc
brackets = enclose lbracket rbracket

--- The document (char c) contains the literal character c.
--- The character should not be a newline (`\n`),
--- the function `line` should be used for line breaks.
--- @param c - a character
--- @return a document which contains the literal character c
char :: Char -> Doc
char c = text [c]

--- The document (string s) concatenates all characters in s using
--- `line` for newline characters and `char` for all
--- other characters. It is used instead of `text` whenever the
--- text contains newline characters.
--- @param s - a string
--- @return a document which contains the string s
string :: String -> Doc
string = hcat . map (\c -> if elem c ['\n','\r'] then line else char c)

--- The document (int i) shows the literal integer i using `text`.
--- @param i - an integer
--- @return a document which contains the integer i
int :: Int -> Doc
int n = text (show n)

--- The document (float f) shows the literal float f using `text`.
--- @param f - a float
--- @return a document which contains the float f
float :: Float -> Doc
float x = text (show x)

--- The document lparen contains a left parenthesis, `"("`.
--- @return a document which contains a left parenthesis
lparen :: Doc
lparen = char '('

--- The document rparen contains a right parenthesis, `")"`.
--- @return a document which contains a right parenthesis
rparen :: Doc
rparen = char ')'

--- The document langle contains a left angle, `"<"`.
--- @return a document which contains a left angle
langle :: Doc
langle = char '<'

--- The document rangle contains a right angle, `">"`.
--- @return a document which contains a right angle
rangle :: Doc
rangle = char '>'

--- The document lbrace contains a left brace, `"{"`.
--- @return a document which contains a left brace
lbrace :: Doc
lbrace = char '{'

--- The document rbrace contains a right brace, `"}"`.
--- @return a document which contains a right brace
rbrace :: Doc
rbrace = char '}'

--- The document lbracket contains a left square bracket, `"["`.
--- @return a document which contains a left square bracket
lbracket :: Doc
lbracket = char '['

--- The document rbracket contains a right square bracket, `"]"`.
--- @return a document which contains a right square bracket
rbracket :: Doc
rbracket = char ']'

--- The document squote contains a single quote, `"'"`.
--- @return a document which contains a single quote
squote :: Doc
squote = char '\''

--- The document dquote contains a double quote.
--- @return a document which contains a double quote
dquote :: Doc
dquote = char '\"'

--- The document dquote contains a `'`'` quote.
--- @return a document which contains a `'`'` quote
bquote :: Doc
bquote = char '`'

--- The document semi contains a semi colon, `";"`.
--- @return a document which contains a semi colon
semi :: Doc
semi = char ';'

--- The document colon contains a colon, `":"`.
--- @return a document which contains a colon
colon :: Doc
colon = char ':'

--- The document comma contains a comma, `","`.
--- @return a document which contains a comma
comma :: Doc
comma = char ','

--- The document space contains a single space, `" "`.
---
---     x <+> y   = x <> space <> y
---
--- @return a document which contains a single space
space :: Doc
space = char ' '

--- The document (spaces n) contains n spaces, when n is greater than 0.
--- Otherwise the document is empty.
---
--- @return a document which contains n spaces or the empty document,
---  if n <= 0
spaces :: Int -> Doc
spaces n | n <= 0    = empty
         | otherwise = text $ replicate n ' '

--- The document dot contains a single dot, `"."`.
--- @return a document which contains a single dot
dot :: Doc
dot = char '.'

--- The document backslash contains a back slash, `"\\"`.
--- @return a document which contains a back slash
backslash :: Doc
backslash = char '\\'

--- The document equals contains an equal sign, `"="`.
--- @return a document which contains an equal
equals :: Doc
equals = char '='

--- The document arrow contains an arrow sign, `"->"`.
--- @return a document which contains an arrow sign
arrow :: Doc
arrow = text "->"

--- The document doubleArrow contains an double arrow sign, `"=>"`.
--- @return a document which contains an double arrow sign
doubleArrow :: Doc
doubleArrow = text "=>"

--- The document doubleColon contains a double colon sign, `"::"`.
--- @return a document which contains a double colon sign
doubleColon :: Doc
doubleColon = text "::"

--- The document bar contains a vertical bar sign, `"|"`.
--- @return a document which contains a vertical bar sign
bar :: Doc
bar = char '|'

--- The document at contains a at sign, `"@"`.
--- @return a document which contains a at sign
at :: Doc
at = char '@'

--- The document tilde contains a tilde sign, `"~"`.
--- @return a document which contains a tilde sign
tilde :: Doc
tilde = char '~'

--- The document `(fillBreak i d)` first renders document `d`. It
--- than appends `space`s until the width is equal to `i`. If the
--- width of `d` is already larger than `i`, the nesting level is
--- increased by `i` and a `line` is appended. When we redefine `ptype`
--- in the previous example to use `fillBreak`, we get a useful
--- variation of the previous output:
---
---     ptype (name,tp)
---          = fillBreak 6 (text name) <+> text "::" <+> text tp
---
--- The output will now be:
---
---     let empty  :: Doc
---         nest   :: Int -> Doc -> Doc
---         linebreak
---                :: Doc
---
fillBreak :: Int -> Doc -> Doc
fillBreak i d = d <> fill'
  where w     = width d
        fill' = if w >= i then nest i linebreak
                          else spaces (i - w)

--- The document `(fill i d)` renders document `d`. It than appends
--- `space`s until the width is equal to `i`. If the width of `d` is
--- already larger, nothing is appended. This combinator is quite
--- useful in practice to output a list of bindings. The following
--- example demonstrates this.
---
---     types  = [("empty","Doc")
---              ,("nest","Int -> Doc -> Doc")
---              ,("linebreak","Doc")]
---
---     ptype (name,tp)
---            = fill 6 (text name) <+> text "::" <+> text tp
---
---     test   = text "let" <+> align (vcat (map ptype types))
---
--- Which is layed out as:
---
---     let empty  :: Doc
---         nest   :: Int -> Doc -> Doc
---         linebreak :: Doc
---
fill :: Int -> Doc -> Doc
fill i d = d <> fill'
  where w     = width d
        fill' = if w >= i then empty else spaces (i - w)

--- Compute the width of a given document
width :: Doc -> Int
width (Doc d) = width' 0 $ d Empty
  where width' w Empty           = w
        width' w (Text     s ts) = width' (w + length s) ts
        width' w (Line     s ts) = width' (w + length s) ts
        width' w (Open       ts) = width' w              ts
        width' w (Close      ts) = width' w              ts
        width' w (OpenNest _ ts) = width' w              ts
        width' w (CloseNest  ts) = width' w              ts

-- -----------------------------------------------------------------------------
-- Implementation
-- -----------------------------------------------------------------------------


type Layout         = String
type Horizontal     = Bool
type Remaining      = Int
type Width          = Int
type Position       = Int
type StartPosition  = Int
type EndPosition    = Int
type Out            = Remaining -> Margins -> Layout

-- Type of a `group output function`: Takes information whether group content
-- should be formatted horizontally or vertically and a continuation to output
-- parts of the document which come after the group
type OutGroupPrefix = Horizontal -> Out -> Out
type Margins        = [Int]

-- Token sequence
data Tokens
  = Text  String Tokens
  | Line  String Tokens
  | Open  Tokens
  | Close Tokens
  | Empty
  | OpenNest  (Margins -> Remaining -> Width -> Margins) Tokens
  | CloseNest Tokens

-- Normalise a token sequence using the following rewriting rules:
--
--   Close (Text s ts) => Text s (Close ts)
--   Open  (Text s ts) => Text s (Open  ts)
--   Open  (Close  ts) => ts
--
-- Rewriting moves `Text` tokens in and out of groups. The set of `lines`
-- "belonging" to each group, i.e. the set of layouts is left unchanged.
normalise :: Tokens -> Tokens
normalise = go id
  where
  go co Empty           = co Empty
    -- there should be no deferred opening brackets
  go co (Open       ts) = go (co . open) ts
  go co (Close      ts) = go (co . Close) ts
  go co (Line     s ts) = co . Line s . go id $ ts
  go co (Text     s ts) = Text s (go co ts)
  go co (OpenNest f ts) = OpenNest f (go co ts)
  go co (CloseNest  ts) = CloseNest (go co ts)

  open t = case t of Close ts -> ts; _ -> Open t

-- Transform a document into a group-closed document by normalising its token
-- sequence.
-- A document is called group-closed, if between the end of every `group` and
-- the next `text` document there is always a `line` document.
doc2Tokens :: Doc -> Tokens
doc2Tokens (Doc d) = normalise (d Empty)

--- `(pretty w d)` pretty prints document `d` with a page width of `w` characters
--- @param w - width of page
--- @param d - a document
--- @return pretty printed document
pretty :: Width -> Doc -> Layout
pretty w d = noGroup (doc2Tokens d) w 1 w [0]

-- Compute number of visible ASCII characters
length :: String -> Int
length = Prelude.length . filter isVisible
  where
  isVisible c = ord c `notElem` ([5, 6, 7] ++ [16 .. 31])

-- Basic pretty printing algorithm:
--
-- 1. Determine for each group in the document its width, i.e. the space it
--    requires for printing if it was printed horizontally, all in one line.
-- 2. Traverse document tree and keep track of remaining free space in current
--    output line.
--    At the start of a group compare remaining space with width of the group:
--    If the width is smaller or equal, the group is formatted horizontally,
--    otherwise vertically.

-- Determine widths of all groups and produce actual layout by traversing token
-- sequence a single time using continuations:
-- At the start of each group construct a `group output function` which receives
-- formate information and information about the remaining space at the
-- beginning of the group.
-- Since groups can be nested we don't want to update a width value for each
-- surrounding group when processing a token. Instead we introduce an absolute
-- measure of a token's position: The width of a group is the difference between
-- the position of its `Close` token and the position of its `Open` token.
-- When traversing the document only the `group output function` of the
-- innermost group is extended. All the other `group output function`s are
-- passed on unchanged. When we come across a `Close` token we merge the
-- function for the innermost group with the function for the next inner group.

-- noGroup is used when there is currently no deferred group
noGroup :: Tokens -> Width -> Position -> Out
noGroup Empty           _ _ _ _  = ""
noGroup (Text     t ts) w p r ms = t ++ noGroup ts w (p + l) (r - l) ms
  where l = length t
noGroup (Line     _ _ ) _ _ _ []       = error "Pretty.noGroup: illegal line"
noGroup (Line     _ ts) w p _ ms@(m:_) =
  '\n' : replicate m ' ' ++ noGroup ts w (p + 1) (w - m) ms
noGroup (Open       ts) w p r ms = oneGroup ts w p (p+r) (\_ c -> c) r ms
noGroup (Close      ts) w p r ms = noGroup ts w p r ms -- may have been pruned
noGroup (OpenNest f ts) w p r ms = noGroup ts w p r (f ms r w)
noGroup (CloseNest  ts) w p r ms = noGroup ts w p r (tail ms)

-- oneGroup is used when there is one deferred group
-- Whenever the tokens `Text` or `Line` are processed, i.e. the current position
-- is increased, pruneOne checks whether whether the group still fits the line
-- Furthermore the `group output function` is extended with the current token
oneGroup :: Tokens -> Width -> Position -> EndPosition -> OutGroupPrefix -> Out
oneGroup Empty           _ _ _ _         = error "Pretty.oneGroup: Empty"
oneGroup (Text     s ts) w p e outGrpPre =
  pruneOne ts w (p + l) e (\h c -> outGrpPre h (outText c))
  where
  l = length s
  outText c r ms = s ++ c (r - l) ms
oneGroup (Line     s ts) w p e outGrpPre =
  pruneOne ts w (p + l) e (\h c -> outGrpPre h (outLine h c))
  where
  l = length s
  outLine _ _ _ []       = error "Pretty.oneGroup.outLine: empty margins"
  outLine h c r ms@(m:_) = if h then s ++ c (r - l) ms
                                else '\n' : replicate m ' ' ++ c (w - m) ms
oneGroup (Open       ts) w p e outGrpPre =
  multiGroup ts w p e outGrpPre Q.empty p (\_ c -> c)
oneGroup (Close      ts) w p e outGrpPre = outGrpPre (p <= e) (noGroup ts w p)
oneGroup (OpenNest f ts) w p e outGrpPre = oneGroup ts w p e
  (\h c -> outGrpPre h (\r ms -> c r (f ms r w)))
oneGroup (CloseNest  ts) w p e outGrpPre = oneGroup ts w p e
  (\h c -> outGrpPre h (\r ms -> c r (tail ms)))

-- multiGroup is used when there are at least two deferred groups
-- Whenever the tokens `Text` or `Line` are processed, i.e. the current position
-- is increased, pruneMulti checks whether whether the outermost group still
-- fits the line.
-- Furthermore the `group output function` of the innermost group is extended
-- with the current token.
-- When we come across a `Open` token during traversal of the token sequence,
-- the current innermost `group output function` is added to the queue.
-- Reaching a `Close` token it is checked whether the queue still contains a
-- deferred `group output function`: If the queue is empty, there is only one
-- group left, otherwise there are at least two groups left.
-- In both cases the function for the innermost group is merged with the
-- function for the next inner group
multiGroup :: Tokens -> Width -> Position -> EndPosition -> OutGroupPrefix
           -> Queue (StartPosition, OutGroupPrefix)
           -> StartPosition -> OutGroupPrefix -> Out
multiGroup Empty       _ _ _ _              _  _ _
  = error "Pretty.multiGroup: Empty"
multiGroup (Text t ts) w p e outGrpPreOuter qs s outGrpPreInner
  = pruneMulti ts w (p+l) e outGrpPreOuter qs s
    (\h c -> outGrpPreInner h (outText c))
  where
  l = length t
  outText c r ms = t ++ c (r-l) ms
multiGroup (Line s ts) w p e outGrpPreOuter qs si outGrpPreInner =
  pruneMulti ts w (p + lens) e outGrpPreOuter qs si
    (\h c -> outGrpPreInner h (outLine h c))
  where
  lens = length s
  outLine _ _ _ []       = error "Pretty.multiGroup.outLine: empty margins"
  outLine h c r ms@(m:_) =
    if h then s ++ c (r-lens) ms else '\n': replicate m ' ' ++ c (w-m) ms
multiGroup (Open ts) w p e outGrpPreOuter qs si outGrpPreInner =
  multiGroup ts w p e outGrpPreOuter (cons (si,outGrpPreInner) qs) p (\_ c -> c)
multiGroup (Close ts) w p e outGrpPreOuter qs si outGrpPreInner =
  case matchHead qs of
    Nothing -> oneGroup ts w p e
                 (\h c -> outGrpPreOuter h
                            (\ri -> outGrpPreInner (p<=si+ri) c ri))
    Just ((s,outGrpPre),qs') ->
      multiGroup ts w p e outGrpPreOuter qs' s
        (\h c -> outGrpPre h (\ri -> outGrpPreInner (p<=si+ri) c ri))
multiGroup (OpenNest f ts) w p e outGrpPreOuter qs si outGrpPreInner =
  multiGroup ts w p e outGrpPreOuter qs si
    (\h c -> outGrpPreInner h (\r ms -> c r (f ms r w)))
multiGroup (CloseNest ts) w p e outGrpPreOuter qs si outGrpPreInner =
  multiGroup ts w p e outGrpPreOuter qs si
    (\h c -> outGrpPreInner h (\r ms -> c r (tail ms)))

-- pruneOne checks whether the outermost group (in this case there is only one
-- group) still fits in the current line. If it doesn't fit, it applies the
-- corresponding `group output function` (the group is formatted vertically)
-- and continues processing the token sequence
pruneOne :: Tokens -> Width -> Position -> EndPosition -> OutGroupPrefix -> Out
pruneOne ts w p e outGrpPre | p <= e    = oneGroup ts w p e outGrpPre
                            | otherwise = outGrpPre False (noGroup ts w p)

-- pruneMulti checks whether the outermost group (in this case there are at
-- least two groups) still fits in the current line. If it doesn't fit, it
-- applies the corresponding `group output function` (the last queue entry) and
-- continues checking whether the next outermost group fits
pruneMulti :: Tokens -> Width -> Position -> EndPosition -> OutGroupPrefix
              -> Queue (StartPosition, OutGroupPrefix)
              -> StartPosition -> OutGroupPrefix -> Out
pruneMulti ts w p e outGrpPreOuter qs si outGrpPreInner
  | p <= e    = multiGroup ts w p e outGrpPreOuter qs si outGrpPreInner
  | otherwise = outGrpPreOuter False (\r ->
                   (case matchLast qs of
                      Nothing -> pruneOne ts w p (si+r) outGrpPreInner
                      Just ((s,outGrpPre),qs') ->
                        pruneMulti ts w p (s+r) outGrpPre qs' si outGrpPreInner)
                          r)
