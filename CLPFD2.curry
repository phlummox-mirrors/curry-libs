module CLPFD2
  ( allDifferent, channel, domain, fdc, sorted, sum
  , (+#), (-#), (*#), (/#), (%#), abs
  , (=#), (/=#), (<#), (<=#), (>#), (>=#), (/\), (\/), neg
  , (!#)
  , loopall, forall
  , solveFD, solveFDVars, solveFDND
  , Option (..)
  ) where

infix  9 !#
infixl 7 *#
infixl 6 +#, -#
infix  4 =#, /=#, <#, <=#, >#, >=#
infixr 3 /\
infixr 2 \/

-- abstract type for FD expressions
data FDExpr

-- abstract type for FD constraints
data FDConstr

-- returns infinite list of FDVars
domain :: Int -> Int -> [FDExpr]
domain l u = ((prim_FD_domain $## l) $## u) unknown

prim_FD_domain :: Int -> Int -> Int -> [FDExpr]
prim_FD_domain external

allDifferent :: [FDExpr] -> FDConstr
allDifferent vs = prim_FD_allDifferent $!! (ensureSpine vs)

prim_FD_allDifferent :: [FDExpr] -> FDConstr
prim_FD_allDifferent external

sum :: [FDExpr] -> FDExpr
sum vs = prim_FD_sum $!! (ensureSpine vs)

prim_FD_sum :: [FDExpr] -> FDExpr
prim_FD_sum external

sorted :: [FDExpr] -> FDConstr
sorted vs = prim_FD_sorted $!! (ensureSpine vs)

prim_FD_sorted :: [FDExpr] -> FDConstr
prim_FD_sorted external

channel :: FDConstr -> FDExpr
channel c = prim_FD_channel $!! c

prim_FD_channel :: FDConstr -> FDExpr
prim_FD_channel external

-- generates a FD expression for the given integer value
fdc :: Int -> FDExpr
fdc v = prim_fdc $## v

prim_fdc :: Int -> FDExpr
prim_fdc external

(+#) :: FDExpr -> FDExpr -> FDExpr
x +# y = (prim_FD_plus $!! x) $!! y

prim_FD_plus :: FDExpr -> FDExpr -> FDExpr
prim_FD_plus external

(-#) :: FDExpr -> FDExpr -> FDExpr
x -# y = (prim_FD_minus $!! x) $!! y

prim_FD_minus :: FDExpr -> FDExpr -> FDExpr
prim_FD_minus external

(*#) :: FDExpr -> FDExpr -> FDExpr
x *# y = (prim_FD_mult $!! x) $!! y

(/#) :: FDExpr -> FDExpr -> FDExpr
x /# y = (prim_FD_div $!! x) $!! y

prim_FD_div :: FDExpr -> FDExpr -> FDExpr
prim_FD_div external

(%#) :: FDExpr -> FDExpr -> FDExpr
x %# y = (prim_FD_mod $!! x) $!! y

prim_FD_mod :: FDExpr -> FDExpr -> FDExpr
prim_FD_mod external

abs :: FDExpr -> FDExpr
abs x = prim_FD_abs $!! x

prim_FD_abs :: FDExpr -> FDExpr
prim_FD_abs external

prim_FD_mult :: FDExpr -> FDExpr -> FDExpr
prim_FD_mult external

(=#) :: FDExpr -> FDExpr -> FDConstr
x =# y = (prim_FD_equal $!! x) $!! y

prim_FD_equal :: FDExpr -> FDExpr -> FDConstr
prim_FD_equal external

(/=#) :: FDExpr -> FDExpr -> FDConstr
x /=# y = (prim_FD_diff $!! x) $!! y

prim_FD_diff :: FDExpr -> FDExpr -> FDConstr
prim_FD_diff external

(<#) :: FDExpr -> FDExpr -> FDConstr
x <# y = (prim_FD_less $!! x) $!! y

prim_FD_less :: FDExpr -> FDExpr -> FDConstr
prim_FD_less external

(<=#) :: FDExpr -> FDExpr -> FDConstr
x <=# y = (prim_FD_lessEqual $!! x) $!! y

prim_FD_lessEqual :: FDExpr -> FDExpr -> FDConstr
prim_FD_lessEqual external

(>#) :: FDExpr -> FDExpr -> FDConstr
x ># y = y <# x

(>=#) :: FDExpr -> FDExpr -> FDConstr
x >=# y = y <=# x

(!#) :: [FDExpr] -> FDExpr -> FDExpr
c !# e = (prim_FD_at $!! (ensureSpine c)) $!! e

prim_FD_at :: [FDExpr] -> FDExpr -> FDExpr
prim_FD_at external

loopall :: FDExpr -> FDExpr -> (FDExpr -> FDConstr) -> FDConstr
loopall from to constr = ((prim_FD_loopall $!! from) $!! to) $!! constr

prim_FD_loopall :: FDExpr -> FDExpr -> (FDExpr -> FDConstr) -> FDConstr
prim_FD_loopall external

forall :: [FDExpr] -> (FDExpr -> FDConstr) -> FDConstr
forall vs constr = (prim_FD_forall $!! vs) $!! constr

prim_FD_forall :: [FDExpr] -> (FDExpr -> FDConstr) -> FDConstr
prim_FD_forall external

(/\) :: FDConstr -> FDConstr -> FDConstr
c1 /\ c2 = (prim_FD_and $!! c1) $!! c2

prim_FD_and :: FDConstr -> FDConstr -> FDConstr
prim_FD_and external

(\/) :: FDConstr -> FDConstr -> FDConstr
c1 \/ c2 = (prim_FD_or $!! c1) $!! c2

prim_FD_or :: FDConstr -> FDConstr -> FDConstr
prim_FD_or external

neg :: FDConstr -> FDConstr
neg c = prim_FD_neg $!! c

prim_FD_neg :: FDConstr -> FDConstr
prim_FD_neg external

solveFD :: [Option] -> FDConstr -> [[Int]]
solveFD external

solveFDVars :: [Option] -> FDConstr -> [FDExpr] -> [[Int]]
solveFDVars external

solveFDND :: [Option] -> FDConstr -> (FDExpr -> Int)
solveFDND opts constr v = solveFDND' opts constr v unknown

solveFDND' :: [Option] -> FDConstr -> FDExpr -> Int -> Int
solveFDND' external

-- labeling and solving options:
-- if no option is given, the Overton solver with in order labeling,
-- depth-first search and first solution search transformer is used
data Option
  -- FD solver back ends
  = Overton
  | GecodeRuntime
  | GecodeSearch
  -- Labeling strategies
  | InOrder
  | FirstFail
  | MiddleOut
  | EndsOut
  -- search strategies
  | DepthFirst
  | BreadthFirst
  -- search transformers
  | FirstSolution
  | AllSolutions