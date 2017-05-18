----------------------------------------------------------------------------
--- The standard prelude of Curry (with type classes).
--- All top-level functions, data types, classes and methods defined
--- in this module are always available in any Curry program.
---
--- @category general
----------------------------------------------------------------------------
{-# OPTIONS_CYMAKE -Wno-incomplete-patterns -Wno-overlapping #-}

module Prelude
  (
    -- classes and overloaded functions
    Eq(..)
  , elem, notElem, lookup
  , Ord(..)
  , Show(..), print, shows, showChar, showString, showParen
  , Read (..), ReadS, lex, read, reads, readParen
  , Bounded (..), Enum (..), boundedEnumFrom, boundedEnumFromThen
  , asTypeOf
  , Num(..), Fractional(..), Real(..), Integral(..)
  -- data types
  , Bool (..) , Char (..) , Int (..) , Float (..), String , Ordering (..)
  , Success, Maybe (..), Either (..), IO (..), IOError (..)
  , DET
  -- functions
  , (.), id, const, curry, uncurry, flip, until, seq, ensureNotFree
  , ensureSpine, ($), ($!), ($!!), ($#), ($##), error
  , failed, (&&), (||), not, otherwise, if_then_else, solve
  , fst, snd, head, tail, null, (++), length, (!!), map, foldl, foldl1
  , foldr, foldr1, filter, zip, zip3, zipWith, zipWith3, unzip, unzip3
  , concat, concatMap, iterate, repeat, replicate, take, drop, splitAt
  , takeWhile, dropWhile, span, break, lines, unlines, words, unwords
  , reverse, and, or, any, all
  , ord, chr, (=:=), success, (&), (&>), maybe
  , either, (>>=), return, (>>), done, putChar, getChar, readFile
  , writeFile, appendFile
  , putStr, putStrLn, getLine, userError, ioError, showError
  , catch, doSolve, sequenceIO, sequenceIO_, mapIO
  , mapIO_, (?), anyOf, unknown
  , when, unless, forIO, forIO_, liftIO, foldIO
  , normalForm, groundNormalForm, apply, cond, (=:<=)
  , enumFrom_, enumFromTo_, enumFromThen_, enumFromThenTo_, negate_, negateFloat
  , PEVAL
  , Monad(..)
  , Functor(..)
  ) where


-- Lines beginning with "--++" are part of the prelude
-- but cannot parsed by the compiler

-- Infix operator declarations:

infixl 9 !!
infixr 9 .
infixl 7 *, `div`, `mod`, `quot`, `rem`, /
infixl 6 +, -
-- infixr 5 :                          -- declared together with list
infixr 5 ++
infix  4 =:=, ==, /=, <, >, <=, >=, =:<=
infix  4 `elem`, `notElem`
infixr 3 &&
infixr 2 ||
infixl 1 >>, >>=
infixr 0 $, $!, $!!, $#, $##, `seq`, &, &>, ?


-- externally defined types for numbers and characters
data Int
data Float
data Char

type String = [Char]

-- Some standard combinators:

--- Function composition.
(.)   :: (b -> c) -> (a -> b) -> (a -> c)
f . g = \x -> f (g x)

--- Identity function.
id              :: a -> a
id x            = x

--- Constant function.
const           :: a -> _ -> a
const x _       = x

--- Converts an uncurried function to a curried function.
curry           :: ((a,b) -> c) -> a -> b -> c
curry f a b     =  f (a,b)

--- Converts an curried function to a function on pairs.
uncurry         :: (a -> b -> c) -> (a,b) -> c
uncurry f (a,b) = f a b

--- (flip f) is identical to f but with the order of arguments reversed.
flip            :: (a -> b -> c) -> b -> a -> c
flip  f x y     = f y x

--- Repeats application of a function until a predicate holds.
until          :: (a -> Bool) -> (a -> a) -> a -> a
until p f x     = if p x then x else until p f (f x)

--- Evaluates the first argument to head normal form (which could also
--- be a free variable) and returns the second argument.
seq     :: _ -> a -> a
x `seq` y = const y $! x

--- Evaluates the argument to head normal form and returns it.
--- Suspends until the result is bound to a non-variable term.
ensureNotFree :: a -> a
ensureNotFree external

--- Evaluates the argument to spine form and returns it.
--- Suspends until the result is bound to a non-variable spine.
ensureSpine :: [a] -> [a]
ensureSpine l = ensureList (ensureNotFree l)
 where ensureList []     = []
       ensureList (x:xs) = x : ensureSpine xs

--- Right-associative application.
($)     :: (a -> b) -> a -> b
f $ x   = f x

--- Right-associative application with strict evaluation of its argument
--- to head normal form.
($!)    :: (a -> b) -> a -> b
($!) external

--- Right-associative application with strict evaluation of its argument
--- to normal form.
($!!)   :: (a -> b) -> a -> b
($!!) external

--- Right-associative application with strict evaluation of its argument
--- to a non-variable term.
($#)    :: (a -> b) -> a -> b
f $# x  = f $! (ensureNotFree x)

--- Right-associative application with strict evaluation of its argument
--- to ground normal form.
($##)   :: (a -> b) -> a -> b
($##) external

--- Aborts the execution with an error message.
error :: String -> _
error x = prim_error $## x

prim_error    :: String -> _
prim_error external

--- A non-reducible polymorphic function.
--- It is useful to express a failure in a search branch of the execution.
--- It could be defined by: `failed = head []`
failed :: _
failed external


-- Boolean values
-- already defined as builtin, since it is required for if-then-else
data Bool = False | True
 deriving (Eq, Ord, Show, Read)

--- Sequential conjunction on Booleans.
(&&)            :: Bool -> Bool -> Bool
True  && x      = x
False && _      = False


--- Sequential disjunction on Booleans.
(||)            :: Bool -> Bool -> Bool
True  || _      = True
False || x      = x


--- Negation on Booleans.
not             :: Bool -> Bool
not True        = False
not False       = True

--- Useful name for the last condition in a sequence of conditional equations.
otherwise       :: Bool
otherwise       = True


--- The standard conditional. It suspends if the condition is a free variable.
if_then_else           :: Bool -> a -> a -> a
if_then_else b t f = case b of True  -> t
                               False -> f

--- Enforce a Boolean condition to be true.
--- The computation fails if the argument evaluates to `False`.
solve :: Bool -> Bool
solve True = True

--- Conditional expression.
--- An expression like `(c &> e)` is evaluated by evaluating the first
--- argument to `True` and then evaluating `e`.
--- The expression has no value if the condition does not evaluate to `True`.
(&>) :: Bool -> a -> a
True &> x = x

--- The equational constraint.
--- `(e1 =:= e2)` is satisfiable if both sides `e1` and `e2` can be
--- reduced to a unifiable data term (i.e., a term without defined
--- function symbols).
(=:=)   :: a -> a -> Bool
(=:=) external

--- Concurrent conjunction.
--- An expression like `(c1 & c2)` is evaluated by evaluating
--- the `c1` and `c2` in a concurrent manner.
(&)     :: Bool -> Bool -> Bool
(&) external

-- used for comparison of standard types like Int, Float and Char
eqChar :: Char -> Char -> Bool
eqChar external

eqInt :: Int -> Int -> Bool
eqInt external

eqFloat :: Float -> Float -> Bool
eqFloat external

--- Ordering type. Useful as a result of comparison functions.
data Ordering = LT | EQ | GT
 deriving (Eq, Ord, Show, Read)

-- used for comparison of standard types like Int, Float and Char
ltEqChar :: Char -> Char -> Bool
ltEqChar external

ltEqInt :: Int -> Int -> Bool
ltEqInt external

ltEqFloat :: Float -> Float -> Bool
ltEqFloat external

-- Pairs

--++ data (a,b) = (a,b)

--- Selects the first component of a pair.
fst             :: (a,_) -> a
fst (x,_)       = x

--- Selects the second component of a pair.
snd             :: (_,b) -> b
snd (_,y)       = y


-- Unit type
--++ data () = ()


-- Lists

--++ data [a] = [] | a : [a]

--- Computes the first element of a list.
head            :: [a] -> a
head (x:_)      = x

--- Computes the remaining elements of a list.
tail            :: [a] -> [a]
tail (_:xs)     = xs

--- Is a list empty?
null            :: [_] -> Bool
null []         = True
null (_:_)      = False

--- Concatenates two lists.
--- Since it is flexible, it could be also used to split a list
--- into two sublists etc.
(++)            :: [a] -> [a] -> [a]
[]     ++ ys    = ys
(x:xs) ++ ys    = x : xs++ys

--- Computes the length of a list.
--length          :: [_] -> Int
--length []       = 0
--length (_:xs)   = 1 + length xs

length :: [_] -> Int
length xs = len xs 0
  where
    len []     n = n
    len (_:ys) n = let np1 = n + 1 in len ys $!! np1

--- List index (subscript) operator, head has index 0.
(!!)            :: [a] -> Int -> a
(x:xs) !! n | n==0      = x
            | n>0       = xs !! (n-1)

--- Map a function on all elements of a list.
map             :: (a->b) -> [a] -> [b]
map _ []        = []
map f (x:xs)    = f x : map f xs

--- Accumulates all list elements by applying a binary operator from
--- left to right. Thus,
---
---     foldl f z [x1,x2,...,xn] = (...((z `f` x1) `f` x2) ...) `f` xn
foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl _ z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

--- Accumulates a non-empty list from left to right.
foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)  = foldl f x xs

--- Accumulates all list elements by applying a binary operator from
--- right to left. Thus,
---
---     foldr f z [x1,x2,...,xn] = (x1 `f` (x2 `f` ... (xn `f` z)...))
foldr            :: (a->b->b) -> b -> [a] -> b
foldr _ z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

--- Accumulates a non-empty list from right to left:
foldr1                :: (a -> a -> a) -> [a] -> a
foldr1 _ [x]          = x
foldr1 f (x:xs@(_:_)) = f x (foldr1 f xs)

--- Filters all elements satisfying a given predicate in a list.
filter            :: (a -> Bool) -> [a] -> [a]
filter _ []       = []
filter p (x:xs)   = if p x then x : filter p xs
                           else filter p xs

--- Joins two lists into one list of pairs. If one input list is shorter than
--- the other, the additional elements of the longer list are discarded.
zip               :: [a] -> [b] -> [(a,b)]
zip []     _      = []
zip (_:_)  []     = []
zip (x:xs) (y:ys) = (x,y) : zip xs ys

--- Joins three lists into one list of triples. If one input list is shorter
--- than the other, the additional elements of the longer lists are discarded.
zip3                      :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3 []     _      _      = []
zip3 (_:_)  []     _      = []
zip3 (_:_)  (_:_)  []     = []
zip3 (x:xs) (y:ys) (z:zs) = (x,y,z) : zip3 xs ys zs

--- Joins two lists into one list by applying a combination function to
--- corresponding pairs of elements. Thus `zip = zipWith (,)`
zipWith                 :: (a->b->c) -> [a] -> [b] -> [c]
zipWith _ []     _      = []
zipWith _ (_:_)  []     = []
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys

--- Joins three lists into one list by applying a combination function to
--- corresponding triples of elements. Thus `zip3 = zipWith3 (,,)`
zipWith3                        :: (a->b->c->d) -> [a] -> [b] -> [c] -> [d]
zipWith3 _ []     _      _      = []
zipWith3 _ (_:_)  []     _      = []
zipWith3 _ (_:_)  (_:_)  []     = []
zipWith3 f (x:xs) (y:ys) (z:zs) = f x y z : zipWith3 f xs ys zs

--- Transforms a list of pairs into a pair of lists.
unzip               :: [(a,b)] -> ([a],[b])
unzip []            = ([],[])
unzip ((x,y):ps)    = (x:xs,y:ys) where (xs,ys) = unzip ps

--- Transforms a list of triples into a triple of lists.
unzip3              :: [(a,b,c)] -> ([a],[b],[c])
unzip3 []           = ([],[],[])
unzip3 ((x,y,z):ts) = (x:xs,y:ys,z:zs) where (xs,ys,zs) = unzip3 ts

--- Concatenates a list of lists into one list.
concat            :: [[a]] -> [a]
concat l          = foldr (++) [] l

--- Maps a function from elements to lists and merges the result into one list.
concatMap         :: (a -> [b]) -> [a] -> [b]
concatMap f       = concat . map f

--- Infinite list of repeated applications of a function f to an element x.
--- Thus, `iterate f x = [x, f x, f (f x),...]`
iterate           :: (a -> a) -> a -> [a]
iterate f x       = x : iterate f (f x)

--- Infinite list where all elements have the same value.
--- Thus, `repeat x = [x, x, x,...]`
repeat            :: a -> [a]
repeat x          = x : repeat x

--- List of length n where all elements have the same value.
replicate         :: Int -> a -> [a]
replicate n x     = take n (repeat x)

--- Returns prefix of length n.
take              :: Int -> [a] -> [a]
take n l          = if n<=0 then [] else takep n l
   where takep _ []     = []
         takep m (x:xs) = x : take (m-1) xs

--- Returns suffix without first n elements.
drop :: Int -> [a] -> [a]
drop n xs = if n<=0 then xs
                    else case xs of []     -> []
                                    (_:ys) -> drop (n-1) ys

--- (splitAt n xs) is equivalent to (take n xs, drop n xs)
splitAt           :: Int -> [a] -> ([a],[a])
splitAt n l       = if n<=0 then ([],l) else splitAtp n l
   where splitAtp _ []     = ([],[])
         splitAtp m (x:xs) = let (ys,zs) = splitAt (m-1) xs in (x:ys,zs)

--- Returns longest prefix with elements satisfying a predicate.
takeWhile          :: (a -> Bool) -> [a] -> [a]
takeWhile _ []     = []
takeWhile p (x:xs) = if p x then x : takeWhile p xs else []

--- Returns suffix without takeWhile prefix.
dropWhile          :: (a -> Bool) -> [a] -> [a]
dropWhile _ []     = []
dropWhile p (x:xs) = if p x then dropWhile p xs else x:xs

--- (span p xs) is equivalent to (takeWhile p xs, dropWhile p xs)
span               :: (a -> Bool) -> [a] -> ([a],[a])
span _ []          = ([],[])
span p (x:xs)
       | p x       = let (ys,zs) = span p xs in (x:ys, zs)
       | otherwise = ([],x:xs)

--- (break p xs) is equivalent to (takeWhile (not.p) xs, dropWhile (not.p) xs).
--- Thus, it breaks a list at the first occurrence of an element satisfying p.
break              :: (a -> Bool) -> [a] -> ([a],[a])
break p            = span (not . p)

--- Breaks a string into a list of lines where a line is terminated at a
--- newline character. The resulting lines do not contain newline characters.
lines        :: String -> [String]
lines []     = []
lines (x:xs) = let (l,xs_l) = splitline (x:xs) in l : lines xs_l
 where splitline []     = ([],[])
       splitline (c:cs) = if c=='\n'
                          then ([],cs)
                          else let (ds,es) = splitline cs in (c:ds,es)

--- Concatenates a list of strings with terminating newlines.
unlines    :: [String] -> String
unlines ls = concatMap (++"\n") ls

--- Breaks a string into a list of words where the words are delimited by
--- white spaces.
words      :: String -> [String]
words s    = let s1 = dropWhile isSpace s
              in if s1=="" then []
                           else let (w,s2) = break isSpace s1
                                 in w : words s2
 where
   isSpace c = c == ' '  || c == '\t' || c == '\n' || c == '\r'

--- Concatenates a list of strings with a blank between two strings.
unwords    :: [String] -> String
unwords ws = if ws==[] then []
                       else foldr1 (\w s -> w ++ ' ':s) ws

--- Reverses the order of all elements in a list.
reverse    :: [a] -> [a]
reverse    = foldl (flip (:)) []

--- Computes the conjunction of a Boolean list.
and        :: [Bool] -> Bool
and        = foldr (&&) True

--- Computes the disjunction of a Boolean list.
or         :: [Bool] -> Bool
or         = foldr (||) False

--- Is there an element in a list satisfying a given predicate?
any        :: (a -> Bool) -> [a] -> Bool
any p      = or . map p

--- Is a given predicate satisfied by all elements in a list?
all        :: (a -> Bool) -> [a] -> Bool
all p      = and . map p

--- Element of a list?
elem :: Eq a => a -> [a] -> Bool
elem x = any (x ==)

--- Not element of a list?
notElem :: Eq a => a -> [a] -> Bool
notElem x = all (x /=)

--- Looks up a key in an association list.
lookup :: Eq a => a -> [(a, b)] -> Maybe b
lookup _ []       = Nothing
lookup k ((x,y):xys)
      | k==x      = Just y
      | otherwise = lookup k xys

--- Generates an infinite sequence of ascending integers.
enumFrom_ :: Int -> [Int]                   -- [n..]
enumFrom_ n = n : enumFrom_ (n+1)

--- Generates an infinite sequence of integers with a particular in/decrement.
enumFromThen_ :: Int -> Int -> [Int]            -- [n1,n2..]
enumFromThen_ n1 n2 = iterate ((n2-n1)+) n1

--- Generates a sequence of ascending integers.
enumFromTo_ :: Int -> Int -> [Int]            -- [n..m]
enumFromTo_ n m = if n>m then [] else n : enumFromTo_ (n+1) m

--- Generates a sequence of integers with a particular in/decrement.
enumFromThenTo_ :: Int -> Int -> Int -> [Int]     -- [n1,n2..m]
enumFromThenTo_ n1 n2 m = takeWhile p (enumFromThen_ n1 n2)
 where
  p x | n2 >= n1  = (x <= m)
      | otherwise = (x >= m)


--- Converts a character into its ASCII value.
ord :: Char -> Int
ord c = prim_ord $# c

prim_ord :: Char -> Int
prim_ord external

--- Converts a Unicode value into a character, fails iff the value is out of bounds
chr :: Int -> Char
chr n | n >= 0 = prim_chr $# n
-- chr n | n < 0 || n > 1114111 = failed
--       | otherwise = prim_chr $# n

prim_chr :: Int -> Char
prim_chr external


-- Types of primitive arithmetic functions and predicates

--- Adds two integers.
(+$)   :: Int -> Int -> Int
(+$) external

--- Subtracts two integers.
(-$)   :: Int -> Int -> Int
(-$) external

--- Multiplies two integers.
(*$)   :: Int -> Int -> Int
(*$) external

--- Integer division. The value is the integer quotient of its arguments
--- and always truncated towards negative infinity.
--- Thus, the value of <code>13 `div` 5</code> is <code>2</code>,
--- and the value of <code>-15 `div` 4</code> is <code>-3</code>.
div_   :: Int -> Int -> Int
div_ external

--- Integer remainder. The value is the remainder of the integer division and
--- it obeys the rule <code>x `mod` y = x - y * (x `div` y)</code>.
--- Thus, the value of <code>13 `mod` 5</code> is <code>3</code>,
--- and the value of <code>-15 `mod` 4</code> is <code>-3</code>.
mod_   :: Int -> Int -> Int
mod_ external

--- Returns an integer (quotient,remainder) pair.
--- The value is the integer quotient of its arguments
--- and always truncated towards negative infinity.
divMod_ :: Int -> Int -> (Int, Int)
divMod_ external

--- Integer division. The value is the integer quotient of its arguments
--- and always truncated towards zero.
--- Thus, the value of <code>13 `quot` 5</code> is <code>2</code>,
--- and the value of <code>-15 `quot` 4</code> is <code>-3</code>.
quot_ :: Int -> Int -> Int
quot_ external

--- Integer remainder. The value is the remainder of the integer division and
--- it obeys the rule <code>x `rem` y = x - y * (x `quot` y)</code>.
--- Thus, the value of <code>13 `rem` 5</code> is <code>3</code>,
--- and the value of <code>-15 `rem` 4</code> is <code>-3</code>.
rem_ :: Int -> Int -> Int
rem_ external

--- Returns an integer (quotient,remainder) pair.
--- The value is the integer quotient of its arguments
--- and always truncated towards zero.
quotRem_ :: Int -> Int -> (Int, Int)
quotRem_ external

--- Unary minus. Usually written as "- e".
negate_ :: Int -> Int
negate_ x = 0 - x

--- Unary minus on Floats. Usually written as "-e".
negateFloat :: Float -> Float
negateFloat external

-- Constraints (included for backward compatibility)
type Success = Bool

--- The always satisfiable constraint.
success :: Success
success = True

-- Maybe type

data Maybe a = Nothing | Just a
 deriving (Eq, Ord, Show, Read)

maybe              :: b -> (a -> b) -> Maybe a -> b
maybe n _ Nothing  = n
maybe _ f (Just x) = f x


-- Either type

data Either a b = Left a | Right b
 deriving (Eq, Ord, Show, Read)

either               :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x)  = f x
either _ g (Right x) = g x


-- Monadic IO

data IO _  -- conceptually: World -> (a,World)

--- Sequential composition of IO actions.
--- @param a - An action
--- @param fa - A function from a value into an action
--- @return An action that first performs a (yielding result r)
---         and then performs (fa r)
(>>=$)             :: IO a -> (a -> IO b) -> IO b
(>>=$) external

--- The empty IO action that directly returns its argument.
returnIO            :: a -> IO a
returnIO external

--- Sequential composition of IO actions.
--- @param a1 - An IO action
--- @param a2 - An IO action
--- @return An IO action that first performs a1 and then a2
(>>$) :: IO _ -> IO b -> IO b
a >>$ b = a >>=$ (\_ -> b)

--- The empty IO action that returns nothing.
done :: IO ()
done = return ()

--- An action that puts its character argument on standard output.
putChar           :: Char -> IO ()
putChar c = prim_putChar $# c

prim_putChar           :: Char -> IO ()
prim_putChar external

--- An action that reads a character from standard output and returns it.
getChar           :: IO Char
getChar external

--- An action that (lazily) reads a file and returns its contents.
readFile          :: String -> IO String
readFile f = prim_readFile $## f

prim_readFile          :: String -> IO String
prim_readFile external

--- An action that writes a file.
--- @param filename - The name of the file to be written.
--- @param contents - The contents to be written to the file.
writeFile         :: String -> String -> IO ()
writeFile f s = (prim_writeFile $## f) s

prim_writeFile         :: String -> String -> IO ()
prim_writeFile external

--- An action that appends a string to a file.
--- It behaves like writeFile if the file does not exist.
--- @param filename - The name of the file to be written.
--- @param contents - The contents to be appended to the file.
appendFile        :: String -> String -> IO ()
appendFile f s = (prim_appendFile $## f) s

prim_appendFile         :: String -> String -> IO ()
prim_appendFile external

--- Action to print a string on stdout.
putStr            :: String -> IO ()
putStr []         = done
putStr (c:cs)     = putChar c >> putStr cs

--- Action to print a string with a newline on stdout.
putStrLn          :: String -> IO ()
putStrLn cs       = putStr cs >> putChar '\n'

--- Action to read a line from stdin.
getLine           :: IO String
getLine           = do c <- getChar
                       if c=='\n' then return []
                                  else do cs <- getLine
                                          return (c:cs)

----------------------------------------------------------------------------
-- Error handling in the I/O monad:

--- The (abstract) type of error values.
--- Currently, it distinguishes between general IO errors,
--- user-generated errors (see 'userError'), failures and non-determinism
--- errors during IO computations. These errors can be caught by 'catch'
--- and shown by 'showError'.
--- Each error contains a string shortly explaining the error.
--- This type might be extended in the future to distinguish
--- further error situations.
data IOError
  = IOError     String -- normal IO error
  | UserError   String -- user-specified error
  | FailError   String -- failing computation
  | NondetError String -- non-deterministic computation

--- A user error value is created by providing a description of the
--- error situation as a string.
userError :: String -> IOError
userError s = UserError s

--- Raises an I/O exception with a given error value.
ioError :: IOError -> IO _
ioError err = prim_ioError $## err

prim_ioError :: IOError -> IO _
prim_ioError external

--- Shows an error values as a string.
showError :: IOError -> String
showError (IOError     s) = "i/o error: "    ++ s
showError (UserError   s) = "user error: "   ++ s
showError (FailError   s) = "fail error: "   ++ s
showError (NondetError s) = "nondet error: " ++ s

--- Catches a possible error or failure during the execution of an
--- I/O action. `(catch act errfun)` executes the I/O action
--- `act`. If an exception or failure occurs
--- during this I/O action, the function `errfun` is applied
--- to the error value.
catch :: IO a -> (IOError -> IO a) -> IO a
catch external

----------------------------------------------------------------------------

--- Converts an arbitrary term into an external string representation.
show_    :: _ -> String
show_ x = prim_show $## x

prim_show    :: _ -> String
prim_show external

--- Converts a term into a string and prints it.
print :: Show a => a -> IO ()
print t = putStrLn (show t)

--- Solves a constraint as an I/O action.
--- Note: the constraint should be always solvable in a deterministic way
doSolve :: Bool -> IO ()
doSolve b | b = done


-- IO monad auxiliary functions:

--- Executes a sequence of I/O actions and collects all results in a list.
sequenceIO       :: [IO a] -> IO [a]
sequenceIO []     = return []
sequenceIO (c:cs) = do x  <- c
                       xs <- sequenceIO cs
                       return (x:xs)

--- Executes a sequence of I/O actions and ignores the results.
sequenceIO_        :: [IO _] -> IO ()
sequenceIO_         = foldr (>>) done

--- Maps an I/O action function on a list of elements.
--- The results of all I/O actions are collected in a list.
mapIO             :: (a -> IO b) -> [a] -> IO [b]
mapIO f            = sequenceIO . map f

--- Maps an I/O action function on a list of elements.
--- The results of all I/O actions are ignored.
mapIO_            :: (a -> IO _) -> [a] -> IO ()
mapIO_ f           = sequenceIO_ . map f

--- Folds a list of elements using an binary I/O action and a value
--- for the empty list.
foldIO :: (a -> b -> IO a) -> a -> [b] -> IO a
foldIO _ a []      =  return a
foldIO f a (x:xs)  =  f a x >>= \fax -> foldIO f fax xs

--- Apply a pure function to the result of an I/O action.
liftIO :: (a -> b) -> IO a -> IO b
liftIO f m = m >>= return . f

--- Like `mapIO`, but with flipped arguments.
---
--- This can be useful if the definition of the function is longer
--- than those of the list, like in
---
--- forIO [1..10] $ \n -> do
---   ...
forIO :: [a] -> (a -> IO b) -> IO [b]
forIO xs f = mapIO f xs

--- Like `mapIO_`, but with flipped arguments.
---
--- This can be useful if the definition of the function is longer
--- than those of the list, like in
---
--- forIO_ [1..10] $ \n -> do
---   ...
forIO_ :: [a] -> (a -> IO b) -> IO ()
forIO_ xs f = mapIO_ f xs

--- Performs an `IO` action unless the condition is met.
unless :: Bool -> IO () -> IO ()
unless p act = if p then done else act

--- Performs an `IO` action when the condition is met.
when :: Bool -> IO () -> IO ()
when p act = if p then act else done

----------------------------------------------------------------
-- Non-determinism and free variables:

--- Non-deterministic choice _par excellence_.
--- The value of `x ? y` is either `x` or `y`.
--- @param x - The right argument.
--- @param y - The left argument.
--- @return either `x` or `y` non-deterministically.
(?)   :: a -> a -> a
x ? _ = x
_ ? y = y

-- Returns non-deterministically any element of a list.
anyOf :: [a] -> a
anyOf = foldr1 (?)

--- Evaluates to a fresh free variable.
unknown :: _
unknown = let x free in x

----------------------------------------------------------------
--- Identity type synonym used to mark deterministic operations.
type DET a = a

--- Identity function used by the partial evaluator
--- to mark expressions to be partially evaluated.
PEVAL   :: a -> a
PEVAL x = x

--- Evaluates the argument to normal form and returns it.
normalForm :: a -> a
normalForm x = id $!! x

--- Evaluates the argument to ground normal form and returns it.
--- Suspends as long as the normal form of the argument is not ground.
groundNormalForm :: a -> a
groundNormalForm x = id $## x

-- Only for internal use:
-- Representation of higher-order applications in FlatCurry.
apply :: (a -> b) -> a -> b
apply external

-- Only for internal use:
-- Representation of conditional rules in FlatCurry.
cond :: Bool -> a -> a
cond external

--- Non-strict equational constraint. Used to implement functional patterns.
(=:<=) :: a -> a -> Bool
(=:<=) external

-- -------------------------------------------------------------------------
-- Eq class and related instances and functions
-- -------------------------------------------------------------------------

class Eq a where
  (==), (/=) :: a -> a -> Bool

  x == y = not (x /= y)
  x /= y = not (x == y)

instance Eq Char where
  c == c' = c `eqChar` c'

instance Eq Int where
  i == i' = i `eqInt` i'

instance Eq Float where
  f == f' = f `eqFloat` f'

instance Eq a => Eq [a] where
  []    == []    = True
  []    == (_:_) = False
  (_:_) == []    = False
  (x:xs) == (y:ys) = x == y && xs == ys

instance Eq () where
  () == () = True

instance (Eq a, Eq b) => Eq (a, b) where
  (a, b) == (a', b') = a == a' && b == b'

instance (Eq a, Eq b, Eq c) => Eq (a, b, c) where
  (a, b, c) == (a', b', c') = a == a' && b == b' && c == c'

instance (Eq a, Eq b, Eq c, Eq d) => Eq (a, b, c, d) where
  (a, b, c, d) == (a', b', c', d') = a == a' && b == b' && c == c' && d == d'

instance (Eq a, Eq b, Eq c, Eq d, Eq e) => Eq (a, b, c, d, e) where
  (a, b, c, d, e) == (a', b', c', d', e') = a == a' && b == b' && c == c' && d == d' && e == e'

instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => Eq (a, b, c, d, e, f) where
  (a, b, c, d, e, f) == (a', b', c', d', e', f') = a == a' && b == b' && c == c' && d == d' && e == e' && f == f'

instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g) => Eq (a, b, c, d, e, f, g) where
  (a, b, c, d, e, f, g) == (a', b', c', d', e', f', g') = a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g'

-- -------------------------------------------------------------------------
-- Ord class and related instances and functions
-- -------------------------------------------------------------------------

--- minimal complete definition: compare or <=
class Eq a => Ord a where
  compare :: a -> a -> Ordering
  (<=) :: a -> a -> Bool
  (>=) :: a -> a -> Bool
  (<)  :: a -> a -> Bool
  (>)  :: a -> a -> Bool

  min :: a -> a -> a
  max :: a -> a -> a

  x < y = x <= y && x /= y
  x > y = not (x <= y)
  x >= y = y <= x
  x <= y = compare x y == EQ || compare x y == LT

  compare x y | x == y = EQ
              | x <= y = LT
              | otherwise = GT

  min x y | x <= y    = x
          | otherwise = y

  max x y | x >= y    = x
          | otherwise = y

instance Ord Char where
  c1 <= c2 = c1 `ltEqChar` c2

instance Ord Int where
  i1 <= i2 = i1 `ltEqInt` i2

instance Ord Float where
  f1 <= f2 = f1 `ltEqFloat` f2

instance Ord a => Ord [a] where
  []    <= []    = True
  (_:_) <= []    = False
  []    <= (_:_) = True
  (x:xs) <= (y:ys) | x == y    = xs <= ys
                   | otherwise = x < y

instance Ord () where
  () <= () = True

instance (Ord a, Ord b) => Ord (a, b) where
  (a, b) <= (a', b') = a < a' || (a == a' && b <= b')

instance (Ord a, Ord b, Ord c) => Ord (a, b, c) where
  (a, b, c) <= (a', b', c') = a < a'
     || (a == a' && b < b')
     || (a == a' && b == b' && c <= c')

instance (Ord a, Ord b, Ord c, Ord d) => Ord (a, b, c, d) where
  (a, b, c, d) <= (a', b', c', d') = a < a'
     || (a == a' && b < b')
     || (a == a' && b == b' && c < c')
     || (a == a' && b == b' && c == c' && d <= d')

instance (Ord a, Ord b, Ord c, Ord d, Ord e) => Ord (a, b, c, d, e) where
  (a, b, c, d, e) <= (a', b', c', d', e') = a < a'
     || (a == a' && b < b')
     || (a == a' && b == b' && c < c')
     || (a == a' && b == b' && c == c' && d < d')
     || (a == a' && b == b' && c == c' && d == d' && e <= e')

-- -------------------------------------------------------------------------
-- Show class and related instances and functions
-- -------------------------------------------------------------------------

type ShowS = String -> String

class Show a where
  show :: a -> String

  showsPrec :: Int -> a -> ShowS

  showList :: [a] -> ShowS

  showsPrec _ x s = show x ++ s
  show x = shows x ""
  showList ls s = showList' shows ls s

showList' :: (a -> ShowS) ->  [a] -> ShowS
showList' _     []     s = "[]" ++ s
showList' showx (x:xs) s = '[' : showx x (showl xs)
  where
    showl []     = ']' : s
    showl (y:ys) = ',' : showx y (showl ys)

shows :: Show a => a -> ShowS
shows = showsPrec 0

showChar :: Char -> ShowS
showChar c s = c:s

showString :: String -> ShowS
showString str s = foldr showChar s str

showParen :: Bool -> ShowS -> ShowS
showParen b s = if b then showChar '(' . s . showChar ')' else s

-- -------------------------------------------------------------------------

instance Show () where
  showsPrec _ () = showString "()"

instance (Show a, Show b) => Show (a, b) where
  showsPrec _ (a, b) = showTuple [shows a, shows b]

instance (Show a, Show b, Show c) => Show (a, b, c) where
  showsPrec _ (a, b, c) = showTuple [shows a, shows b, shows c]

instance (Show a, Show b, Show c, Show d) => Show (a, b, c, d) where
  showsPrec _ (a, b, c, d) = showTuple [shows a, shows b, shows c, shows d]

instance (Show a, Show b, Show c, Show d, Show e) => Show (a, b, c, d, e) where
  showsPrec _ (a, b, c, d, e) = showTuple [shows a, shows b, shows c, shows d, shows e]

instance Show a => Show [a] where
  showsPrec _ = showList

instance Show Char where
  -- TODO: own implementation instead of passing to original Prelude functions?
  showsPrec _ c = showString (show_ c)

  showList cs | null cs   = showString "\"\""
              | otherwise = showString (show_ cs)

instance Show Int where
  showsPrec = showSigned (showString . show_)

instance Show Float where
  showsPrec = showSigned (showString . show_)

showSigned :: Real a => (a -> ShowS) -> Int -> a -> ShowS
showSigned showPos p x
  | x < 0     = showParen (p > 6) (showChar '-' . showPos (-x))
  | otherwise = showPos x

showTuple :: [ShowS] -> ShowS
showTuple ss = showChar '('
             . foldr1 (\s r -> s . showChar ',' . r) ss
             . showChar ')'

appPrec :: Int
appPrec = 10

appPrec1 :: Int
appPrec1 = 11

-- -------------------------------------------------------------------------
-- Read class and related instances and functions
-- -------------------------------------------------------------------------

type ReadS a = String -> [(a, String)]


class Read a where
  readsPrec :: Int -> ReadS a

  readList :: ReadS [a]
  readList = readListDefault

readListDefault :: Read a => ReadS [a]
readListDefault = readParen False (\r -> [pr | ("[",s)  <- lex r
                                        , pr       <- readl s])
    where readl s = [([], t) | ("]", t) <- lex s] ++
                      [(x : xs, u) | (x, t) <- reads s, (xs, u) <- readl' t]
          readl' s = [([], t) | ("]", t) <- lex s] ++
                       [(x : xs, v) | (",", t)  <- lex s, (x, u) <- reads t
                                    , (xs,v) <- readl' u]

reads :: Read a => ReadS a
reads = readsPrec 0

readParen :: Bool -> ReadS a -> ReadS a
readParen b g = if b then mandatory else optional
  where optional r = g r ++ mandatory r
        mandatory r =
          [(x, u) | ("(", s) <- lex r, (x, t) <- optional s, (")", u) <- lex t]

read :: (Read a) => String -> a
read s =  case [x | (x, t) <- reads s, ("", "") <- lex t] of
  [x] -> x
  [] -> error "Prelude.read: no parse"
  _ -> error "Prelude.read: ambiguous parse"

instance Read () where
  readsPrec _ = readParen False (\r -> [ ((), t) | ("(", s) <- lex r
                                                 , (")", t) <- lex s ])

instance Read Int where
  readsPrec _ = readSigned (\s -> [(i,t) | (x,t) <- lexDigits s
                                         , (i,[]) <- readNatLiteral x])

instance Read Float where
  readsPrec _ = readSigned
                  (\s -> [ (f,t) | (x,t) <- lex s, not (null x)
                                 , isDigit (head x), (f,[]) <- readFloat x ])
   where
    readFloat x = if all isDigit x
                    then [ (i2f i, t) | (i,t) <- readNatLiteral x ]
                    else readFloatLiteral x

readSigned :: Real a => ReadS a -> ReadS a
readSigned p = readParen False read'
  where read' r = read'' r ++ [(-x, t) | ("-", s) <- lex r, (x, t) <- read'' s]
        read'' r = [(n, s) | (str, s) <- lex r, (n, "") <- p str]

instance Read Char where
  readsPrec _ = readParen False
                  (\s -> [ (c, t) | (x, t) <- lex s, not (null x), head x == '\''
                                  , (c, []) <- readCharLiteral x ])

  readList s = readParen False
                 (\s -> [ (cs, t) | (x, t) <- lex s, not (null x), head x == '"'
                                  , (cs, []) <- readStringLiteral x ]) s
                ++
               readListDefault s

-- Primitive operations to read specific literals.
readNatLiteral :: ReadS Int
readNatLiteral s = prim_readNatLiteral $## s

prim_readNatLiteral :: String -> [(Int,String)]
prim_readNatLiteral external

readFloatLiteral :: ReadS Float
readFloatLiteral s = prim_readFloatLiteral $## s

prim_readFloatLiteral :: String -> [(Float,String)]
prim_readFloatLiteral external

readCharLiteral :: ReadS Char
readCharLiteral s = prim_readCharLiteral $## s

prim_readCharLiteral :: String -> [(Char,String)]
prim_readCharLiteral external

readStringLiteral :: ReadS String
readStringLiteral s = prim_readStringLiteral $## s

prim_readStringLiteral :: String -> [(String,String)]
prim_readStringLiteral external

instance Read a => Read [a] where
  readsPrec _ = readList

instance (Read a, Read b) => Read (a, b) where
  readsPrec _ = readParen False (\r -> [ ((a, b), w) | ("(", s) <- lex r
                                                     , (a, t) <- reads s
                                                     , (",", u) <- lex t
                                                     , (b, v) <- reads u
                                                     , (")", w) <- lex v ])

instance (Read a, Read b, Read c) => Read (a, b, c) where
  readsPrec _ = readParen False (\r -> [ ((a, b, c), y) | ("(", s) <- lex r
                                                        , (a, t) <- reads s
                                                        , (",", u) <- lex t
                                                        , (b, v) <- reads u
                                                        , (",", w) <- lex v
                                                        , (c, x) <- reads w
                                                        , (")", y) <- lex x ])

instance (Read a, Read b, Read c, Read d) => Read (a, b, c, d) where
  readsPrec _ = readParen False
                  (\q -> [ ((a, b, c, d), z) | ("(", r) <- lex q
                                             , (a, s) <- reads r
                                             , (",", t) <- lex s
                                             , (b, u) <- reads t
                                             , (",", v) <- lex u
                                             , (c, w) <- reads v
                                             , (",", x) <- lex w
                                             , (d, y) <- reads x
                                             , (")", z) <- lex y ])

instance (Read a, Read b, Read c, Read d, Read e) => Read (a, b, c, d, e) where
  readsPrec _ = readParen False
                  (\o -> [ ((a, b, c, d, e), z) | ("(", p) <- lex o
                                                , (a, q) <- reads p
                                                , (",", r) <- lex q
                                                , (b, s) <- reads r
                                                , (",", t) <- lex s
                                                , (c, u) <- reads t
                                                , (",", v) <- lex u
                                                , (d, w) <- reads v
                                                , (",", x) <- lex w
                                                , (e, y) <- reads x
                                                , (")", z) <- lex y ])

-- The following definitions are necessary to implement instances of Read.

lex :: ReadS String
lex s = case s of
    "" -> [("","")]
    (c:s)
      | isSpace c -> lex $ dropWhile isSpace s
    ('\'':s) ->
      [('\'' : ch ++ "'", t) | (ch, '\'' : t)  <- lexLitChar s, ch /= "'"]
    ('"':s) -> [('"' : str, t) | (str, t) <- lexString s]
    (c:s)
      | isSingle c -> [([c], s)]
      | isSym c -> [(c : sym, t) | (sym, t) <- [span isSym s]]
      | isAlpha c -> [(c : nam, t) | (nam, t) <- [span isIdChar s]]
      | isDigit c ->
        [(c : ds ++ fe, t)| (ds, s) <- [span isDigit s], (fe, t)  <- lexFracExp s]
      | otherwise -> []
  where
  isSingle c = c `elem` ",;()[]{}_`"
  isSym c = c `elem` "!@#$%&⋆+./<=>?\\^|:-~"
  isIdChar c = isAlphaNum c || c `elem` "_'"
  lexFracExp s = case s of
    ('.':c:cs)
      | isDigit c ->
        [('.' : ds ++ e, u) | (ds, t) <- lexDigits (c : cs), (e, u)  <- lexExp t]
    s -> lexExp s
  lexExp s = case s of
    (e:s) | e `elem` "eE" ->
      [(e : c : ds, u) | (c:t)  <- [s], c `elem` "+-"
                       , (ds, u) <- lexDigits t] ++
        [(e : ds, t) | (ds, t) <- lexDigits s]
    s -> [("", s)]
  lexString s = case s of
    ('"':s) -> [("\"", s)]
    s -> [(ch ++ str, u) | (ch, t) <- lexStrItem s, (str, u) <- lexString t]
  lexStrItem s = case s of
    ('\\':'&':s) -> [("\\&", s)]
    ('\\':c:s)
      | isSpace c -> [("\\&", t) | '\\':t <- [dropWhile isSpace s]]
    s -> lexLitChar s

lexLitChar :: ReadS String
lexLitChar s = case s of
    "" -> []
    ('\\':s) -> map (prefix '\\') (lexEsc s)
    (c:s) -> [([c], s)]
  where
  lexEsc s = case s of
    (c:s)
      | c `elem` "abfnrtv\\\"'" -> [([c], s)]
    ('^':c:s)
      | c >= '@' && c <= '_'    -> [(['^',c], s)]
    ('b':s) -> [prefix 'b' (span isBinDigit s)]
    ('o':s) -> [prefix 'o' (span isOctDigit s)]
    ('x':s) -> [prefix 'x' (span isHexDigit s)]
    s@(d:_)
      | isDigit d -> [span isDigit s]
    s@(c:_)
      | isUpper c -> [span isCharName s]
    _ -> []
  isCharName c = isUpper c || isDigit c
  prefix c (t, s) = (c : t, s)

lexDigits :: ReadS String
lexDigits = nonNull isDigit

nonNull :: (Char -> Bool) -> ReadS String
nonNull p s = [(cs, t) | (cs@(_:_), t) <- [span p s]]

--- Returns true if the argument is an uppercase letter.
isUpper         :: Char -> Bool
isUpper c       =  c >= 'A' && c <= 'Z'

--- Returns true if the argument is an lowercase letter.
isLower         :: Char -> Bool
isLower c       =  c >= 'a' && c <= 'z'

--- Returns true if the argument is a letter.
isAlpha         :: Char -> Bool
isAlpha c       =  isUpper c || isLower c

--- Returns true if the argument is a decimal digit.
isDigit         :: Char -> Bool
isDigit c       =  c >= '0' && c <= '9'

--- Returns true if the argument is a letter or digit.
isAlphaNum      :: Char -> Bool
isAlphaNum c    =  isAlpha c || isDigit c

--- Returns true if the argument is a binary digit.
isBinDigit     :: Char -> Bool
isBinDigit c   =  c >= '0' || c <= '1'

--- Returns true if the argument is an octal digit.
isOctDigit     :: Char -> Bool
isOctDigit c    =  c >= '0' && c <= '7'

--- Returns true if the argument is a hexadecimal digit.
isHexDigit      :: Char -> Bool
isHexDigit c     = isDigit c || c >= 'A' && c <= 'F'
                             || c >= 'a' && c <= 'f'

--- Returns true if the argument is a white space.
isSpace         :: Char -> Bool
isSpace c       =  c == ' '    || c == '\t' || c == '\n' ||
                   c == '\r'   || c == '\f' || c == '\v' ||
                   c == '\xa0' || ord c `elem` [5760,6158,8192,8239,8287,12288]

-- -------------------------------------------------------------------------
-- Bounded and Enum classes and instances
-- -------------------------------------------------------------------------

class Bounded a where
  minBound, maxBound :: a

class Enum a where
  succ :: a -> a
  pred :: a -> a

  toEnum   :: Int -> a
  fromEnum :: a -> Int

  enumFrom       :: a -> [a]
  enumFromThen   :: a -> a -> [a]
  enumFromTo     :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]

  succ = toEnum . (+ 1) . fromEnum
  pred = toEnum . (\x -> x -1) . fromEnum
  enumFrom x = map toEnum [fromEnum x ..]
  enumFromThen x y = map toEnum [fromEnum x, fromEnum y ..]
  enumFromTo x y = map toEnum [fromEnum x .. fromEnum y]
  enumFromThenTo x1 x2 y = map toEnum [fromEnum x1, fromEnum x2 .. fromEnum y]

instance Bounded () where
  minBound = ()
  maxBound = ()

instance Enum () where
  succ _      = error "Prelude.Enum.().succ: bad argument"
  pred _      = error "Prelude.Enum.().pred: bad argument"

  toEnum x | x == 0    = ()
           | otherwise = error "Prelude.Enum.().toEnum: bad argument"

  fromEnum () = 0
  enumFrom ()         = [()]
  enumFromThen () ()  = let many = ():many in many
  enumFromTo () ()    = [()]
  enumFromThenTo () () () = let many = ():many in many

instance Bounded Bool where
  minBound = False
  maxBound = True

instance Enum Bool where
  succ False = True
  succ True  = error "Prelude.Enum.Bool.succ: bad argument"

  pred False = error "Prelude.Enum.Bool.pred: bad argument"
  pred True  = False

  toEnum n | n == 0 = False
           | n == 1 = True
           | otherwise = error "Prelude.Enum.Bool.toEnum: bad argument"

  fromEnum False = 0
  fromEnum True  = 1

  enumFrom = boundedEnumFrom
  enumFromThen = boundedEnumFromThen


instance (Bounded a, Bounded b) => Bounded (a, b) where
  minBound = (minBound, minBound)
  maxBound = (maxBound, maxBound)

instance (Bounded a, Bounded b, Bounded c) => Bounded (a, b, c) where
  minBound = (minBound, minBound, minBound)
  maxBound = (maxBound, maxBound, maxBound)

instance (Bounded a, Bounded b, Bounded c, Bounded d) => Bounded (a, b, c, d) where
  minBound = (minBound, minBound, minBound, minBound)
  maxBound = (maxBound, maxBound, maxBound, maxBound)

instance (Bounded a, Bounded b, Bounded c, Bounded d, Bounded e) => Bounded (a, b, c, d, e) where
  minBound = (minBound, minBound, minBound, minBound, minBound)
  maxBound = (maxBound, maxBound, maxBound, maxBound, maxBound)



instance Bounded Ordering where
  minBound = LT
  maxBound = GT

instance Enum Ordering where
  succ LT = EQ
  succ EQ = GT
  succ GT = error "Prelude.Enum.Ordering.succ: bad argument"

  pred LT = error "Prelude.Enum.Ordering.pred: bad argument"
  pred EQ = LT
  pred GT = EQ

  toEnum n | n == 0 = LT
           | n == 1 = EQ
           | n == 2 = GT
           | otherwise = error "Prelude.Enum.Ordering.toEnum: bad argument"

  fromEnum LT = 0
  fromEnum EQ = 1
  fromEnum GT = 2

  enumFrom = boundedEnumFrom
  enumFromThen = boundedEnumFromThen

uppermostCharacter :: Int
uppermostCharacter = 0x10FFFF

instance Bounded Char where
   minBound = chr 0
   maxBound = chr uppermostCharacter


instance Enum Char where

  succ c | ord c < uppermostCharacter = chr $ ord c + 1
         | otherwise = error "Prelude.Enum.Char.succ: no successor"

  pred c | ord c > 0 = chr $ ord c - 1
         | otherwise = error "Prelude.Enum.Char.succ: no predecessor"

  toEnum = chr
  fromEnum = ord

  enumFrom = boundedEnumFrom
  enumFromThen = boundedEnumFromThen

-- TODO:
-- instance Enum Float where

-- TODO (?):
-- instance Bounded Int where

instance Enum Int where
  -- TODO: is Int unbounded?
  succ x = x + 1
  pred x = x - 1

  -- TODO: correct semantic?
  toEnum n = n
  fromEnum n = n

  -- TODO: provide own implementations?
  enumFrom = enumFrom_
  enumFromTo = enumFromTo_
  enumFromThen = enumFromThen_
  enumFromThenTo = enumFromThenTo_


boundedEnumFrom :: (Enum a, Bounded a) => a -> [a]
boundedEnumFrom n = map toEnum [fromEnum n .. fromEnum (maxBound `asTypeOf` n)]

boundedEnumFromThen :: (Enum a, Bounded a) => a -> a -> [a]
boundedEnumFromThen n1 n2
  | i_n2 >= i_n1  = map toEnum [i_n1, i_n2 .. fromEnum (maxBound `asTypeOf` n1)]
  | otherwise     = map toEnum [i_n1, i_n2 .. fromEnum (minBound `asTypeOf` n1)]
  where
    i_n1 = fromEnum n1
    i_n2 = fromEnum n2

-- -------------------------------------------------------------------------
-- Numeric classes and instances
-- -------------------------------------------------------------------------

-- minimal definition: all (except negate or (-))
class Num a where
  (+), (-), (*) :: a -> a -> a
  negate :: a -> a
  abs :: a -> a
  signum :: a -> a

  fromInteger :: Int -> a

  x - y = x + negate y
  negate x = 0 - x

instance Num Int where
  x + y = x +$ y
  x - y = x -$ y
  x * y = x *$ y

  negate x = 0 - x

  abs x | x >= 0 = x
        | otherwise = negate x

  signum x | x > 0     = 1
           | x == 0    = 0
           | otherwise = -1

  fromInteger x = x

instance Num Float where
  x + y = x +. y
  x - y = x -. y
  x * y = x *. y

  negate x = negateFloat x

  abs x | x >= 0 = x
        | otherwise = negate x


  signum x | x > 0     = 1
           | x == 0    = 0
           | otherwise = -1

  fromInteger x = i2f x

-- minimal definition: fromRational and (recip or (/))
class Num a => Fractional a where

  (/) :: a -> a -> a
  recip :: a -> a

  recip x = 1/x
  x / y = x * recip y

  fromRational :: Float -> a -- since we have no type Rational

instance Fractional Float where
  x / y = x /. y
  recip x = 1.0/x

  fromRational x = x

class (Num a, Ord a) => Real a where
  -- toRational :: a -> Rational

class Real a => Integral a where
  div  :: a -> a -> a
  mod  :: a -> a -> a
  quot :: a -> a -> a
  rem  :: a -> a -> a

  divMod  :: a -> a -> (a, a)
  quotRem :: a -> a -> (a, a)

  n `div`  d = q where (q, _) = divMod n d
  n `mod`  d = r where (_, r) = divMod n d
  n `quot` d = q where (q, _) = n `quotRem` d
  n `rem`  d = r where (_, r) = n `quotRem` d

instance Real Int where
  -- no class methods to implement

instance Real Float where
  -- no class methods to implement

instance Integral Int where
  divMod n d = (n `div_` d, n `mod_` d)
  quotRem n d = (n `quot_` d, n `rem_` d)

-- -------------------------------------------------------------------------
-- Helper functions
-- -------------------------------------------------------------------------

asTypeOf :: a -> a -> a
asTypeOf = const

-- -------------------------------------------------------------------------
-- Floating point operations
-- -------------------------------------------------------------------------

--- Addition on floats.
(+.)   :: Float -> Float -> Float
x +. y = (prim_Float_plus $# y) $# x

prim_Float_plus :: Float -> Float -> Float
prim_Float_plus external

--- Subtraction on floats.
(-.)   :: Float -> Float -> Float
x -. y = (prim_Float_minus $# y) $# x

prim_Float_minus :: Float -> Float -> Float
prim_Float_minus external

--- Multiplication on floats.
(*.)   :: Float -> Float -> Float
x *. y = (prim_Float_times $# y) $# x

prim_Float_times :: Float -> Float -> Float
prim_Float_times external

--- Division on floats.
(/.)   :: Float -> Float -> Float
x /. y = (prim_Float_div $# y) $# x

prim_Float_div :: Float -> Float -> Float
prim_Float_div external

--- Conversion function from integers to floats.
i2f    :: Int -> Float
i2f x = prim_i2f $# x

prim_i2f :: Int -> Float
prim_i2f external

-- the end of the standard prelude

class Functor f where
  fmap :: (a -> b) -> f a -> f b

instance Functor [] where
  fmap = map

class Monad m where
  (>>=) :: m a -> (a -> m b) -> m b
  (>>) :: m a -> m b -> m b
  m >> k = m >>= \_ -> k
  return :: a -> m a
  fail :: String -> m a
  fail s = error s

instance Monad IO where
  a1 >>= a2 = a1 >>=$ a2
  a1 >>  a2 = a1 >>$  a2
  return x = returnIO x

instance Monad Maybe where
  Nothing >>= _ = Nothing
  (Just x) >>= f = f x
  return = Just
  fail _ = Nothing

instance Monad [] where
  xs >>= f = [y | x <- xs, y <- f x]
  return x = [x]
  fail _ = []
