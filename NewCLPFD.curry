module NewCLPFD(runFD, (>>#), (>>=#), osuccess, cval, newVar, newVars,(+#),(-#),(*#),(=#), (/=#), (<#), (<=#), (>#), (>=#), hasValue, allDifferent, sum, labeling) where

-- The operator declarations are similar to the standard arithmetic
-- and relational operators.

infixl 7 *#
infixl 6 +#, -#
infix  4 =#, /=#, <#, <=#, >#, >=#
infixl 1 >>#, >>=#

-- type for FD variables
data FDVar

-- OvertonFD monad
data OvertonFD _

(>>=#) :: OvertonFD a -> (a -> OvertonFD b) -> OvertonFD b
m >>=# f = prim_FD_bind m f

prim_FD_bind :: OvertonFD a -> (a -> OvertonFD b) -> OvertonFD b
prim_FD_bind external

(>>#) :: OvertonFD a -> OvertonFD b -> OvertonFD b
m >># n = m >>=# (\_ -> n)

runFD :: OvertonFD [Int] -> [[Int]]
runFD external

osuccess :: OvertonFD ()
osuccess external

cval :: Int -> OvertonFD FDVar
cval val = prim_cval $!! val

prim_cval :: Int -> OvertonFD FDVar
prim_cval external

newVar :: Int -> Int -> OvertonFD FDVar
newVar l u = (prim_newVar $!! l) $!! u

prim_newVar :: Int -> Int -> OvertonFD FDVar
prim_newVar external

newVars :: Int -> Int -> Int -> OvertonFD [FDVar]
newVars n l u = ((prim_newVars $!! n) $!! l) $!! u

prim_newVars :: Int -> Int -> Int -> OvertonFD [FDVar]
prim_newVars external

hasValue :: FDVar -> Int -> OvertonFD ()
hasValue x n = (prim_hasValue $## x) $!! n

prim_hasValue :: FDVar -> Int -> OvertonFD ()
prim_hasValue external

-- Addition of FD variables.
-- @result - free variable to which the result of x+#y is bound 
(+#)   :: FDVar -> FDVar -> OvertonFD FDVar
x +# y = (prim_FD_plus $## x) $## y

prim_FD_plus :: FDVar -> FDVar -> OvertonFD FDVar
prim_FD_plus external

-- Subtraction of FD variables.
-- @result - free variable to which the result of x-#y is bound
(-#)   :: FDVar -> FDVar -> OvertonFD FDVar
x -# y = (prim_FD_minus $## x) $## y

prim_FD_minus :: FDVar -> FDVar -> OvertonFD FDVar
prim_FD_minus external

-- Multiplication of FD variables.
-- @result - free variable to which the result of x*#y is bound
(*#)   :: FDVar -> FDVar -> OvertonFD FDVar
x *# y = (prim_FD_times $## x) $## y

prim_FD_times :: FDVar -> FDVar -> OvertonFD FDVar
prim_FD_times external

-- Equality of FD variables.
(=#)   :: FDVar -> FDVar -> OvertonFD ()
x =# y = (prim_FD_equal $## x) $## y

prim_FD_equal :: FDVar -> FDVar -> OvertonFD ()
prim_FD_equal external

-- Disequality of FD variables.
(/=#)  :: FDVar -> FDVar -> OvertonFD ()
x /=# y = (prim_FD_notequal $## x) $## y

prim_FD_notequal :: FDVar -> FDVar -> OvertonFD ()
prim_FD_notequal external

-- "Less than" constraint on FD variables.
(<#)   :: FDVar -> FDVar -> OvertonFD ()
x <# y = (prim_FD_le $## x) $## y

prim_FD_le :: FDVar -> FDVar -> OvertonFD ()
prim_FD_le external

-- "Less than or equal" constraint on FD variables.
(<=#)  :: FDVar -> FDVar -> OvertonFD ()
x <=# y = (prim_FD_leq $## x) $## y

prim_FD_leq :: FDVar -> FDVar -> OvertonFD ()
prim_FD_leq external

-- "Greater than" constraint on FD variables.
(>#)   :: FDVar -> FDVar -> OvertonFD ()
x ># y = (prim_FD_ge $## x) $## y

prim_FD_ge :: FDVar -> FDVar -> OvertonFD ()
prim_FD_ge external

-- "Greater than or equal" constraint on FD variables.
(>=#)  :: FDVar -> FDVar -> OvertonFD ()
x >=# y = (prim_FD_geq $## x) $## y

prim_FD_geq :: FDVar -> FDVar -> OvertonFD ()
prim_FD_geq external

-- "All different" constraint on FD variables.
-- @param vs - list of FD variables
-- @return satisfied if the FD variables in the argument list xs
--         have pairwise different values.
allDifferent :: [FDVar] -> OvertonFD ()
allDifferent vs = prim_allDifferent $!! (ensureSpine vs)

prim_allDifferent :: [FDVar] -> OvertonFD ()
prim_allDifferent external

-- "Sum" constraint on FD variables.
-- @param vs - list of FD variables
-- @return   - sum of given variables
-- @result   - free variable to which the result of sum vs is bound 
sum :: [FDVar] -> OvertonFD FDVar
sum vs = prim_sum $!! (ensureSpine vs)

prim_sum :: [FDVar] -> OvertonFD FDVar
prim_sum external

-- label FD variables in order
-- @param vs - list of FD variables (labeling variables)
-- @labelVar - KiCS2-internal the ID of this variable is used for binding solutions to labeling variables
labeling :: [FDVar] -> OvertonFD [Int]
labeling vs = prim_labeling $!! (ensureSpine vs)

prim_labeling :: [FDVar] -> OvertonFD [Int]
prim_labeling external

-- end of library CLPFD
