{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}

import qualified Control.Monad.State as S (State, gets, modify, evalState)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Show (showListWith)

import Debug (internalError)

import qualified Control.CP.ComposableTransformers as MCP (solve)
import Control.CP.EnumTerm (assignments, labelling, inOrder, firstFail, middleOut, endsOut, EnumTerm(..))
import Control.CP.FD.FD (FDInstance, FDSolver(..))
import Control.CP.FD.Interface (labelCol)
import Control.CP.FD.Model (Model, ModelInt, ModelCol, ModelIntTerm(..), ModelFunctions, asExpr)
import Control.CP.FD.OvertonFD.OvertonFD (OvertonFD)
import Control.CP.FD.Solvers (dfs, bfs, it, fs)
import Control.CP.SearchTree (Tree, MonadTree(..))
import Data.Expr.Data (BoolExpr (BoolConst), ColExpr (ColList))
import Data.Expr.Sugar ((!), (@=), (@/=), (@<), (@<=), (@+), (@-), (@*), (@/), (@%), (@&&), (@||), (@:), inv, xsum, channel, allDiff, sorted, list, forall, loopall, ToBoolExpr(..))

#ifdef GECODE
import Control.CP.FD.GecodeExample (setSearchMinimize)
import Control.CP.FD.Gecode.Common (GecodeWrappedSolver)
import Control.CP.FD.Gecode.Runtime (RuntimeGecodeSolver)
import Control.CP.FD.Gecode.RuntimeSearch (SearchGecodeSolver)
#endif

-- -----------------------------------------------------------------------------
-- Representation of FD expressions
-- -----------------------------------------------------------------------------

type FDIdent = Integer

data ArithOp = Plus | Minus | Mult | Div | Mod
  deriving (Eq, Ord)

data C_FDExpr = FDVal Int
              | FDVar FDIdent Domain
              | FDParam FDIdent
              | ExprHole Int
              | FDAt [C_FDExpr] C_FDExpr
              | FDArith ArithOp C_FDExpr C_FDExpr
              | FDAbs C_FDExpr
              | FDSum [C_FDExpr]
              | FDChannel C_FDConstr
              | Choice_C_FDExpr Cover ID C_FDExpr C_FDExpr
              | Choices_C_FDExpr Cover ID [C_FDExpr]
              | Fail_C_FDExpr Cover FailInfo
              | Guard_C_FDExpr Cover Constraints C_FDExpr

instance Show C_FDExpr where
  showsPrec d (Choice_C_FDExpr cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_FDExpr cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_FDExpr cd cs e) = showsGuard d cd cs e
  showsPrec _ (Fail_C_FDExpr _ _) = showChar '!'
  showsPrec _ (FDVal x) = shows x
  showsPrec _ (FDVar i _) = showString $ 'x' : show i
  showsPrec _ (FDParam i) = showString $ 'p' : show i
  showsPrec _ (ExprHole i) = showString $ "par" ++ show i
  showsPrec d (FDAt c e) = showChar '(' . showListWith (showsPrec d) c
    . showChar '!' . showsPrec d e . showChar ')'
  showsPrec d (FDArith op x y) = showChar '(' . showsPrec d x . showArithOP op
    . showsPrec d y . showChar ')'
    where showArithOP Plus  = showString " +# "
          showArithOP Minus = showString " -# "
          showArithOP Mult  = showString " *# "
          showArithOP Div   = showString " /# "
          showArithOP Mod   = showString " %# "
  showsPrec d (FDAbs x) = showChar '(' . showString "abs " . showsPrec d x
    . showChar ')'
  showsPrec d (FDSum xs) = showChar '(' . showString "sum "
    . showListWith (showsPrec d) xs . showChar ')'
  showsPrec d (FDChannel c) = showString "channel " . showChar '('
    . showsPrec d c . showChar ')'

instance Read C_FDExpr where
  readsPrec = internalError "read for FDExpr is undefined"

instance NonDet C_FDExpr where
  choiceCons = Choice_C_FDExpr
  choicesCons = Choices_C_FDExpr
  failCons = Fail_C_FDExpr
  guardCons = Guard_C_FDExpr
  try (Choice_C_FDExpr cd i x y) = tryChoice cd i x y
  try (Choices_C_FDExpr cd i xs) = tryChoices cd i xs
  try (Fail_C_FDExpr cd info) = Fail cd info
  try (Guard_C_FDExpr cd cs e) = Guard cd cs e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_FDExpr cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_FDExpr cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_FDExpr cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_FDExpr _  i@(ChoiceID _) _) = internalError ("CLPFD2.FDExpr.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_FDExpr cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_FDExpr cd cs e) = f cd cs e
  match _ _ _ _ _ f x = f x

instance Generable C_FDExpr where
  generate = internalError "generate for FDExpr is undefined"

instance NormalForm C_FDExpr where
  ($!!) cont x@(FDVal _) d cs = cont x d cs
  ($!!) cont x@(FDVar _ _) d cs = cont x d cs
  ($!!) cont x@(FDParam _) d cs = cont x d cs
  ($!!) cont x@(ExprHole _) d cs = cont x d cs
  ($!!) cont x@(FDAt _ _) d cs = cont x d cs
  ($!!) cont x@(FDArith _ _ _) d cs = cont x d cs
  ($!!) cont x@(FDAbs _) d cs = cont x d cs
  ($!!) cont x@(FDSum _) d cs = cont x d cs
  ($!!) cont x@(FDChannel _) d cs = cont x d cs
  ($!!) cont (Choice_C_FDExpr cd i x y) d cs = nfChoice cont cd i x y cd cs
  ($!!) cont (Choices_C_FDExpr cd i xs) d cs = nfChoices cont cd i xs d cs
  ($!!) cont (Guard_C_FDExpr cd c e) d cs = guardCons cd c (((cont $!! e) d) (addCs c cs))
  ($!!) _ (Fail_C_FDExpr cd info) _ _ = failCons cd info
  ($##) cont x@(FDVal _) d cs = cont x d cs
  ($##) cont x@(FDVar _ _) d cs = cont x d cs
  ($##) cont x@(FDParam _) d cs = cont x d cs
  ($##) cont x@(ExprHole _) d cs = cont x d cs
  ($##) cont x@(FDAt _ _) d cs = cont x d cs
  ($##) cont x@(FDArith _ _ _) d cs = cont x d cs
  ($##) cont x@(FDAbs _) d cs = cont x d cs
  ($##) cont x@(FDSum _) d cs = cont x d cs
  ($##) cont x@(FDChannel _) d cs = cont x d cs
  ($##) cont (Choice_C_FDExpr cd i x y) d cs = gnfChoice cont cd i x y cd cs
  ($##) cont (Choices_C_FDExpr cd i xs) d cs = gnfChoices cont cd i xs d cs
  ($##) cont (Guard_C_FDExpr cd c e) d cs = guardCons cd c (((cont $## e) d) (addCs c cs))
  ($##) _ (Fail_C_FDExpr cd info) _ _ = failCons cd info
  showCons x@(FDVal _) = "CLPFD2.FDVal _"
  showCons x@(FDVar _ _) = "CLPFD2.FDVar _ _"
  showCons x@(FDParam _) = "CLPFD2.FDParam _"
  showCons x@(ExprHole _) = "CLPFD2.ExprHole _"
  showCons x@(FDAt _ _) = "CLPFD2.FDAt _ _"
  showCons x@(FDArith _ _ _) = "CLPFD2.FDArith _ _ _"
  showCons x@(FDAbs _) = "CLPFD2.FDAbs _ _ _"
  showCons x@(FDSum _) = "CLPFD2.FDSum _"
  showCons x@(FDChannel _) = "CLPFD2.FDChannel _"
  showCons x = error ("CLPFD2.FDExpr.showCons: no constructor: " ++ (show x))
  searchNF _ cont x@(FDVal _) = cont x
  searchNF _ cont x@(FDVar _ _) = cont x
  searchNF _ cont x@(FDParam _) = cont x
  searchNF _ cont x@(ExprHole _) = cont x
  searchNF _ cont x@(FDAt _ _) = cont x
  searchNF _ cont x@(FDArith _ _ _) = cont x
  searchNF _ cont x@(FDAbs _) = cont x
  searchNF _ cont x@(FDSum _) = cont x
  searchNF _ cont x@(FDChannel _) = cont x
  searchNF _ _ x = error ("CLPFD2.FDExpr.searchNF: no constructor: " ++ (show x))

instance Unifiable C_FDExpr where
  (=.=)    = internalError "(=.=) for FDExpr is undefined"
  (=.<=)   = internalError "(=.<=) for FDExpr is undefined"
  bind     = internalError "bind for FDExpr is undefined"
  lazyBind = internalError "lazyBind for FDExpr is undefined"
  fromDecision _ _ _ = error "fromDecision for FDExpr is undefined"

instance Curry_Prelude.Curry C_FDExpr where
  (=?=) (Choice_C_FDExpr cd i x y) z d cs = narrow cd i (((x Curry_Prelude.=?= z) d) cs) (((y Curry_Prelude.=?= z) d) cs)
  (=?=) (Choices_C_FDExpr cd i xs) y d cs = narrows cs cd i (\x -> ((x Curry_Prelude.=?= y) d) cs) xs
  (=?=) (Guard_C_FDExpr cd c e) y d cs = guardCons cd c (((e Curry_Prelude.=?= y) d) (addCs c cs))
  (=?=) (Fail_C_FDExpr cd info) _ _ _ = failCons cd info
  (=?=) z (Choice_C_FDExpr cd i x y) d cs = narrow cd i (((z Curry_Prelude.=?= x) d) cs) (((z Curry_Prelude.=?= y) d) cs)
  (=?=) y (Choices_C_FDExpr cd i xs) d cs = narrows cs cd i (\x -> ((y Curry_Prelude.=?= x) d) cs) xs
  (=?=) y (Guard_C_FDExpr cd c e) d cs = guardCons cd c (((y Curry_Prelude.=?= e) d) (addCs c cs))
  (=?=) _ (Fail_C_FDExpr cd info) _ _ = failCons cd info
  (=?=) x y                       _ _ = toCurry (x == y)
  (<?=) (Choice_C_FDExpr cd i x y) z d cs = narrow cd i (((x Curry_Prelude.<?= z) d) cs) (((y Curry_Prelude.<?= z) d) cs)
  (<?=) (Choices_C_FDExpr cd i xs) y d cs = narrows cs cd i (\x -> ((x Curry_Prelude.<?= y) d) cs) xs
  (<?=) (Guard_C_FDExpr cd c e) y d cs = guardCons cd c (((e Curry_Prelude.<?= y) d) (addCs c cs))
  (<?=) (Fail_C_FDExpr cd info) _ _ _ = failCons cd info
  (<?=) z (Choice_C_FDExpr cd i x y) d cs = narrow cd i (((z Curry_Prelude.<?= x) d) cs) (((z Curry_Prelude.<?= y) d) cs)
  (<?=) y (Choices_C_FDExpr cd i xs) d cs = narrows cs cd i (\x -> ((y Curry_Prelude.<?= x) d) cs) xs
  (<?=) y (Guard_C_FDExpr cd c e) d cs = guardCons cd c (((y Curry_Prelude.<?= e) d) (addCs c cs))
  (<?=) _ (Fail_C_FDExpr cd info) _ _ = failCons cd info
  (<?=) x y                       _ _ = toCurry (x <= y)

instance ConvertCurryHaskell C_FDExpr C_FDExpr where
  toCurry   = id
  fromCurry = id

instance ConvertCurryHaskell C_Option C_Option where
  toCurry   = id
  fromCurry = id

-- -----------------------------------------------------------------------------
-- Representation of FD constraints
-- -----------------------------------------------------------------------------

data RelOp = Equal | Diff | Less | LessEqual
  deriving (Eq, Ord)

data C_FDConstr = FDConst Bool
                | FDRel RelOp C_FDExpr C_FDExpr
                | FDAllDifferent [C_FDExpr]
                | FDSorted [C_FDExpr]
                | FDLoopAll C_FDExpr C_FDExpr (C_FDExpr -> C_FDConstr)
                | FDForAll [C_FDExpr] (C_FDExpr -> C_FDConstr)
                | FDAnd C_FDConstr C_FDConstr
                | FDOr C_FDConstr C_FDConstr
                | FDNeg C_FDConstr
                | Choice_C_FDConstr Cover ID C_FDConstr C_FDConstr
                | Choices_C_FDConstr Cover ID [C_FDConstr]
                | Fail_C_FDConstr Cover FailInfo
                | Guard_C_FDConstr Cover Constraints C_FDConstr

instance Show C_FDConstr where
  showsPrec d (Choice_C_FDConstr cd i x y) = showsChoice d cd i x y
  showsPrec d (Choices_C_FDConstr cd i xs) = showsChoices d cd i xs
  showsPrec d (Guard_C_FDConstr cd cs e) = showsGuard d cd cs e
  showsPrec _ (Fail_C_FDConstr _ _) = showChar '!'
  showsPrec _ (FDConst b) = shows b
  showsPrec d (FDRel op x y) = showsPrec d x . showRelOp op . showsPrec d y
    where showRelOp Equal     = showString " =# "
          showRelOp Diff      = showString " /=# "
          showRelOp Less      = showString " <# "
          showRelOp LessEqual = showString " <=# "
  showsPrec d (FDAllDifferent xs) = showString "allDifferent "
                         . showListWith (showsPrec d) xs
  showsPrec d (FDSorted xs) = showString "sorted " . showListWith (showsPrec d) xs
  showsPrec d (FDLoopAll from to constr) = showString "loopall "
                         . showsPrec d from . showString " " . showsPrec d to
                         . showString " (\\par" . shows d . showString " -> "
                         . showsPrec (d+1) (constr (ExprHole d)) . showChar ')'
  showsPrec d (FDForAll xs constr) = showString "loopall "
                         . showListWith (showsPrec d) xs
                         . showString " (\\par" . shows d . showString " -> "
                         . showsPrec (d+1) (constr (ExprHole d)) . showChar ')'
  showsPrec d (FDAnd c1 c2) = showChar '(' . showsPrec d c1 . showString " /\\ "
                             . showsPrec d c2 . showChar ')'
  showsPrec d (FDOr c1 c2) = showChar '(' . showsPrec d c1 . showString " \\/ "
                             . showsPrec d c2 . showChar ')'
  showsPrec d (FDNeg c) = showString "neg(" . showsPrec d c . showChar ')'

instance Read C_FDConstr where
  readsPrec = internalError "read for FDConstr is undefined"

instance NonDet C_FDConstr where
  choiceCons = Choice_C_FDConstr
  choicesCons = Choices_C_FDConstr
  failCons = Fail_C_FDConstr
  guardCons = Guard_C_FDConstr
  try (Choice_C_FDConstr cd i x y) = tryChoice cd i x y
  try (Choices_C_FDConstr cd i xs) = tryChoices cd i xs
  try (Fail_C_FDConstr cd info) = Fail cd info
  try (Guard_C_FDConstr cd cs e) = Guard cd cs e
  try x = Val x
  match f _ _ _ _ _ (Choice_C_FDConstr cd i x y) = f cd i x y
  match _ f _ _ _ _ (Choices_C_FDConstr cd i@(NarrowedID _ _) xs) = f cd i xs
  match _ _ f _ _ _ (Choices_C_FDConstr cd i@(FreeID _ _) xs) = f cd i xs
  match _ _ _ _ _ _ (Choices_C_FDConstr _  i@(ChoiceID _) _) = internalError ("CLPFD2.FDConstr.match: Choices with ChoiceID " ++ (show i))
  match _ _ _ f _ _ (Fail_C_FDConstr cd info) = f cd info
  match _ _ _ _ f _ (Guard_C_FDConstr cd cs e) = f cd cs e
  match _ _ _ _ _ f x = f x

instance Generable C_FDConstr where
  generate = internalError "generate for FDConstr is undefined"

instance NormalForm C_FDConstr where
  ($!!) cont x@(FDConst _) d cs = cont x d cs
  ($!!) cont x@(FDRel _ _ _) d cs = cont x d cs
  ($!!) cont x@(FDAllDifferent _) d cs = cont x d cs
  ($!!) cont x@(FDSorted _) d cs = cont x d cs
  ($!!) cont x@(FDLoopAll _ _ _) d cs = cont x d cs
  ($!!) cont x@(FDForAll _ _) d cs = cont x d cs
  ($!!) cont x@(FDAnd _ _) d cs = cont x d cs
  ($!!) cont x@(FDOr _ _) d cs = cont x d cs
  ($!!) cont x@(FDNeg _) d cs = cont x d cs
  ($!!) cont (Choice_C_FDConstr cd i x y) d cs = nfChoice cont cd i x y cd cs
  ($!!) cont (Choices_C_FDConstr cd i xs) d cs = nfChoices cont cd i xs d cs
  ($!!) cont (Guard_C_FDConstr cd c e) d cs = guardCons cd c (((cont $!! e) d) (addCs c cs))
  ($!!) _ (Fail_C_FDConstr cd info) _ _ = failCons cd info
  ($##) cont x@(FDConst _) d cs = cont x d cs
  ($##) cont x@(FDRel _ _ _) d cs = cont x d cs
  ($##) cont x@(FDAllDifferent _) d cs = cont x d cs
  ($##) cont x@(FDSorted _) d cs = cont x d cs
  ($##) cont x@(FDLoopAll _ _ _) d cs = cont x d cs
  ($##) cont x@(FDForAll _ _) d cs = cont x d cs
  ($##) cont x@(FDAnd _ _) d cs = cont x d cs
  ($##) cont x@(FDOr _ _) d cs = cont x d cs
  ($##) cont x@(FDNeg _) d cs = cont x d cs
  ($##) cont (Choice_C_FDConstr cd i x y) d cs = gnfChoice cont cd i x y cd cs
  ($##) cont (Choices_C_FDConstr cd i xs) d cs = gnfChoices cont cd i xs d cs
  ($##) cont (Guard_C_FDConstr cd c e) d cs = guardCons cd c (((cont $## e) d) (addCs c cs))
  ($##) _ (Fail_C_FDConstr cd info) _ _ = failCons cd info
  showCons x@(FDConst _) = "CLPFD2.FDConst _"
  showCons x@(FDRel _ _ _) = "CLPFD2.FDRel _ _ _"
  showCons x@(FDAllDifferent _) = "CLPFD2.FDAllDifferent _"
  showCons x@(FDSorted _) = "CLPFD2.FDSorted _"
  showCons x@(FDLoopAll _ _ _) = "CLPFD2.FDLoopAll _ _ _"
  showCons x@(FDForAll _ _) = "CLPFD2.FDForAll _ _"
  showCons x@(FDAnd _ _) = "CLPFD2.FDAnd _ _"
  showCons x@(FDOr _ _) = "CLPFD2.FDOr _ _"
  showCons x@(FDNeg _) = "CLPFD2.FDNeg _"
  showCons x = error ("CLPFD2.FDConstr.showCons: no constructor: " ++ (show x))
  searchNF _ cont x@(FDConst _) = cont x
  searchNF _ cont x@(FDRel _ _ _) = cont x
  searchNF _ cont x@(FDAllDifferent _) = cont x
  searchNF _ cont x@(FDSorted _) = cont x
  searchNF _ cont x@(FDLoopAll _ _ _) = cont x
  searchNF _ cont x@(FDForAll _ _) = cont x
  searchNF _ cont x@(FDAnd _ _) = cont x
  searchNF _ cont x@(FDOr _ _) = cont x
  searchNF _ cont x@(FDNeg _) = cont x
  searchNF _ _ x = error ("CLPFD2.FDConstr.searchNF: no constructor: " ++ (show x))

instance Unifiable C_FDConstr where
  (=.=)    = internalError "(=.=) for FDConstr is undefined"
  (=.<=)   = internalError "(=.<=) for FDConstr is undefined"
  bind     = internalError "bind for FDConstr is undefined"
  lazyBind = internalError "lazyBind for FDConstr is undefined"
  fromDecision _ _ _ = error "fromDecision for FDConstr is undefined"

instance Curry_Prelude.Curry C_FDConstr where
  (=?=) (Choice_C_FDConstr cd i x y) z d cs = narrow cd i (((x Curry_Prelude.=?= z) d) cs) (((y Curry_Prelude.=?= z) d) cs)
  (=?=) (Choices_C_FDConstr cd i xs) y d cs = narrows cs cd i (\x -> ((x Curry_Prelude.=?= y) d) cs) xs
  (=?=) (Guard_C_FDConstr cd c e) y d cs = guardCons cd c (((e Curry_Prelude.=?= y) d) (addCs c cs))
  (=?=) (Fail_C_FDConstr cd info) _ _ _ = failCons cd info
  (=?=) z (Choice_C_FDConstr cd i x y) d cs = narrow cd i (((z Curry_Prelude.=?= x) d) cs) (((z Curry_Prelude.=?= y) d) cs)
  (=?=) y (Choices_C_FDConstr cd i xs) d cs = narrows cs cd i (\x -> ((y Curry_Prelude.=?= x) d) cs) xs
  (=?=) y (Guard_C_FDConstr cd c e) d cs = guardCons cd c (((y Curry_Prelude.=?= e) d) (addCs c cs))
  (=?=) _ (Fail_C_FDConstr cd info) _ _ = failCons cd info
  (=?=) x y                         _ _ = toCurry (x == y)
  (<?=) (Choice_C_FDConstr cd i x y) z d cs = narrow cd i (((x Curry_Prelude.<?= z) d) cs) (((y Curry_Prelude.<?= z) d) cs)
  (<?=) (Choices_C_FDConstr cd i xs) y d cs = narrows cs cd i (\x -> ((x Curry_Prelude.<?= y) d) cs) xs
  (<?=) (Guard_C_FDConstr cd c e) y d cs = guardCons cd c (((e Curry_Prelude.<?= y) d) (addCs c cs))
  (<?=) (Fail_C_FDConstr cd info) _ _ _ = failCons cd info
  (<?=) z (Choice_C_FDConstr cd i x y) d cs = narrow cd i (((z Curry_Prelude.<?= x) d) cs) (((z Curry_Prelude.<?= y) d) cs)
  (<?=) y (Choices_C_FDConstr cd i xs) d cs = narrows cs cd i (\x -> ((y Curry_Prelude.<?= x) d) cs) xs
  (<?=) y (Guard_C_FDConstr cd c e) d cs = guardCons cd c (((y Curry_Prelude.<?= e) d) (addCs c cs))
  (<?=) _ (Fail_C_FDConstr cd info) _ _ = failCons cd info
  (<?=) x y                         _ _ = toCurry (x <= y)

-- -----------------------------------------------------------------------------
-- Eq and Ord instances
-- -----------------------------------------------------------------------------

instance Eq C_FDExpr where
  (==) = equalExpr 0

instance Eq C_FDConstr where
  (==) = equalConstr 0

instance Ord C_FDExpr where
  compare = compareExpr 0

instance Ord C_FDConstr where
  compare = compareConstr 0

equalExpr :: Int -> C_FDExpr -> C_FDExpr -> Bool
equalExpr _ (FDVal x)                      (FDVal y)                      = x == y
equalExpr _ (FDVar i _)                    (FDVar j _)                    = i == j
equalExpr _ (FDParam i)                    (FDParam j)                    = i == j
equalExpr _ (ExprHole i)                   (ExprHole j)                   = i == j
equalExpr l (FDAt c1 e1)                   (FDAt c2 e2)                   = equalList l equalExpr c1 c2 && equalExpr l e1 e2
equalExpr l (FDArith op1 x1 y1)            (FDArith op2 x2 y2)            = op1 == op2 && equalExpr l x1 x2 && equalExpr l y1 y2
equalExpr l (FDAbs x1)                     (FDAbs x2)                     = equalExpr l x1 x2
equalExpr l (FDSum xs1)                    (FDSum xs2)                    = equalList l equalExpr xs1 xs2
equalExpr l (FDChannel c1)                 (FDChannel c2)                 = equalConstr l c1 c2
equalExpr l (Choice_C_FDExpr cd1 i1 x1 y1) (Choice_C_FDExpr cd2 i2 x2 y2) = cd1 == cd2 && i1 == i2 && equalExpr l x1 x2 && equalExpr l y1 y2
equalExpr l (Choices_C_FDExpr cd1 i1 xs1)  (Choices_C_FDExpr cd2 i2 xs2)  = cd1 == cd2 && i1 == i2 && equalList l equalExpr xs1 xs2
equalExpr _ (Fail_C_FDExpr cd1 info1)      (Fail_C_FDExpr cd2 info2)      = cd1 == cd2 && info1 == info2
equalExpr l (Guard_C_FDExpr cd1 cs1 x1)    (Guard_C_FDExpr cd2 cs2 x2)    = cd1 == cd2 && cs1 == cs2 && equalExpr l x1 x2
equalExpr _ _                              _                              = False

equalList :: Int -> (Int -> a -> a -> Bool) -> [a] -> [a] -> Bool
equalList _ _  []     []     = True
equalList l eq (x:xs) (y:ys) = eq l x y && equalList l eq xs ys

equalConstr :: Int -> C_FDConstr -> C_FDConstr -> Bool
equalConstr _ (FDConst b1)                     (FDConst b2)                     = b1 == b2
equalConstr l (FDRel op1 x1 y1)                (FDRel op2 x2 y2)                = op1 == op2 && equalExpr l x1 x2 && equalExpr l y1 y2
equalConstr l (FDAllDifferent xs1)             (FDAllDifferent xs2)             = equalList l equalExpr xs1 xs2
equalConstr l (FDSorted xs1)                   (FDSorted xs2)                   = equalList l equalExpr xs1 xs2
equalConstr l (FDLoopAll f1 t1 c1)             (FDLoopAll f2 t2 c2)             = equalExpr l f1 f2 && equalExpr l t1 t2 && equalConstr (l+1) (c1 (ExprHole l)) (c2 (ExprHole l))
equalConstr l (FDForAll xs1 c1)                (FDForAll xs2 c2)                = equalList l equalExpr xs1 xs2 && equalConstr (l+1) (c1 (ExprHole l)) (c2 (ExprHole l))
equalConstr l (FDAnd c1 d1)                    (FDAnd c2 d2)                    = equalConstr l c1 c2 && equalConstr l d1 d2
equalConstr l (FDOr c1 d1)                     (FDOr c2 d2)                     = equalConstr l c1 c2 && equalConstr l d1 d2
equalConstr l (FDNeg c1)                       (FDNeg c2)                       = equalConstr l c1 c2
equalConstr l (Choice_C_FDConstr cd1 i1 x1 y1) (Choice_C_FDConstr cd2 i2 x2 y2) = cd1 == cd2 && i1 == i2 && equalConstr l x1 x2 && equalConstr l y1 y2
equalConstr l (Choices_C_FDConstr cd1 i1 xs1)  (Choices_C_FDConstr cd2 i2 xs2)  = cd1 == cd2 && i1 == i2 && equalList l equalConstr xs1 xs2
equalConstr _ (Fail_C_FDConstr cd1 info1)      (Fail_C_FDConstr cd2 info2)      = cd1 == cd2 && info1 == info2
equalConstr l (Guard_C_FDConstr cd1 cs1 x1)    (Guard_C_FDConstr cd2 cs2 x2)    = cd1 == cd2 && cs1 == cs2 && equalConstr l x1 x2
equalConstr _ _                                _                                = False

infixr 4 <<>>
(<<>>) :: Ordering -> Ordering -> Ordering
a <<>> b = case a of
  EQ -> b
  _  -> a

compareExpr :: Int -> C_FDExpr -> C_FDExpr -> Ordering
compareExpr _ (FDVal x1)                     (FDVal x2)                     = compare x1 x2
compareExpr _ (FDVal _)                      _                              = LT
compareExpr _ _                              (FDVal _)                      = GT
compareExpr _ (FDVar i1 _)                   (FDVar i2 _)                   = compare i1 i2
compareExpr _ (FDVar _ _)                    _                              = LT
compareExpr _ _                              (FDVar _ _)                    = GT
compareExpr _ (FDParam i1)                   (FDParam i2)                   = compare i1 i2
compareExpr _ (FDParam _)                    _                              = LT
compareExpr _ _                              (FDParam _)                    = GT
compareExpr _ (ExprHole i1)                  (ExprHole i2)                  = compare i1 i2
compareExpr _ (ExprHole _)                   _                              = LT
compareExpr _ _                              (ExprHole _)                   = GT
compareExpr l (FDAt c1 e1)                   (FDAt c2 e2)                   = compareList l compareExpr c1 c2 <<>> compareExpr l e1 e2
compareExpr _ (FDAt _ _)                     _                              = LT
compareExpr _ _                              (FDAt _ _)                     = GT
compareExpr l (FDArith op1 x1 y1)            (FDArith op2 x2 y2)            = compare op1 op2 <<>> compareExpr l x1 x2 <<>> compareExpr l y1 y2
compareExpr _ (FDArith _ _ _)                _                              = LT
compareExpr _ _                              (FDArith _ _ _)                = GT
compareExpr l (FDAbs x1)                     (FDAbs x2)                     = compareExpr l x1 x2
compareExpr _ (FDAbs _)                      _                              = LT
compareExpr _ _                              (FDAbs _)                      = GT
compareExpr l (FDSum xs1)                    (FDSum xs2)                    = compareList l compareExpr xs1 xs2
compareExpr _ (FDSum _)                      _                              = LT
compareExpr _ _                              (FDSum _)                      = GT
compareExpr l (FDChannel b1)                 (FDChannel b2)                 = compareConstr l b1 b2
compareExpr _ (FDChannel _)                  _                              = LT
compareExpr _ _                              (FDChannel _)                  = GT
compareExpr l (Choice_C_FDExpr cd1 i1 x1 y1) (Choice_C_FDExpr cd2 i2 x2 y2) = compare cd1 cd2 <<>> compare (getKey i1) (getKey i2) <<>> compareExpr l x1 x2 <<>> compareExpr l y1 y2
compareExpr _ (Choice_C_FDExpr _ _ _ _)      _                              = LT
compareExpr _ _                              (Choice_C_FDExpr _ _ _ _)      = GT
compareExpr l (Choices_C_FDExpr cd1 i1 xs1)  (Choices_C_FDExpr cd2 i2 xs2)  = compare cd1 cd2 <<>> compare (getKey i1) (getKey i2) <<>> compareList l compareExpr xs1 xs2
compareExpr _ (Choices_C_FDExpr _ _ _)       _                              = LT
compareExpr _ _                              (Choices_C_FDExpr _ _ _)       = GT
compareExpr _ (Fail_C_FDExpr cd1 _)          (Fail_C_FDExpr cd2 _)          = compare cd1 cd2
compareExpr _ (Fail_C_FDExpr _ _)            _                              = LT
compareExpr _ _                              (Fail_C_FDExpr _ _)            = GT
compareExpr l (Guard_C_FDExpr cd1 _ x1)      (Guard_C_FDExpr cd2 _ x2)      = compare cd1 cd2 <<>> compareExpr l x1 x2

compareList :: Int -> (Int -> a -> a -> Ordering) -> [a] -> [a] -> Ordering
compareList _ _  []     []     = EQ
compareList l cp (x:xs) (y:ys) = cp l x y <<>> compareList l cp xs ys

compareConstr :: Int -> C_FDConstr -> C_FDConstr -> Ordering
compareConstr _ (FDConst b1)                     (FDConst b2)                     = compare b1 b2
compareConstr _ (FDConst _)                      _                                = LT
compareConstr _ _                                (FDConst _)                      = GT
compareConstr l (FDRel op1 x1 y1)                (FDRel op2 x2 y2)                = compare op1 op2 <<>> compareExpr l x1 x2 <<>> compareExpr l y1 y2
compareConstr _ (FDRel _ _ _)                    _                                = LT
compareConstr _ _                                (FDRel _ _ _)                    = GT
compareConstr l (FDAllDifferent xs1)             (FDAllDifferent xs2)             = compareList l compareExpr xs1 xs2
compareConstr _ (FDAllDifferent _)               _                                = LT
compareConstr _ _                                (FDAllDifferent _)               = GT
compareConstr l (FDSorted xs1)                   (FDSorted xs2)                   = compareList l compareExpr xs1 xs2
compareConstr _ (FDSorted _)                     _                                = LT
compareConstr _ _                                (FDSorted _)                     = GT
compareConstr l (FDLoopAll f1 t1 c1)             (FDLoopAll f2 t2 c2)             = compareExpr l f1 f2 <<>> compareExpr l t1 t2 <<>> compareConstr (l+1) (c1 (ExprHole l)) (c2 (ExprHole l))
compareConstr _ (FDLoopAll _ _ _)                _                                = LT
compareConstr _ _                                (FDLoopAll _ _ _)                = GT
compareConstr l (FDForAll xs1 c1)                (FDForAll xs2 c2)                = compareList l compareExpr xs1 xs2 <<>> compareConstr (l+1) (c1 (ExprHole l)) (c2 (ExprHole l))
compareConstr _ (FDForAll _ _)                   _                                = LT
compareConstr _ _                                (FDForAll _ _)                   = GT
compareConstr l (FDAnd c1 d1)                    (FDAnd c2 d2)                    = compareConstr l c1 c2 <<>> compareConstr l d1 d2
compareConstr _ (FDAnd _ _)                      _                                = LT
compareConstr _ _                                (FDAnd _ _)                      = GT
compareConstr l (FDOr c1 d1)                     (FDOr c2 d2)                     = compareConstr l c1 c2 <<>> compareConstr l d1 d2
compareConstr _ (FDOr _ _)                       _                                = LT
compareConstr _ _                                (FDOr _ _)                       = GT
compareConstr l (FDNeg c1)                       (FDNeg c2)                       = compareConstr l c1 c2
compareConstr _ (FDNeg _)                        _                                = LT
compareConstr _ _                                (FDNeg _)                        = GT
compareConstr l (Choice_C_FDConstr cd1 i1 x1 y1) (Choice_C_FDConstr cd2 i2 x2 y2) = compare cd1 cd2 <<>> compare (getKey i1) (getKey i2) <<>> compareConstr l x1 x2 <<>> compareConstr l y1 y2
compareConstr _ (Choice_C_FDConstr _ _ _ _)      _                                = LT
compareConstr _ _                                (Choice_C_FDConstr _ _ _ _)      = GT
compareConstr l (Choices_C_FDConstr cd1 i1 xs1)  (Choices_C_FDConstr cd2 i2 xs2)  = compare cd1 cd2 <<>> compare (getKey i1) (getKey i2) <<>> compareList l compareConstr xs1 xs2
compareConstr _ (Choices_C_FDConstr _ _ _)       _                                = LT
compareConstr _ _                                (Choices_C_FDConstr _ _ _)       = GT
compareConstr _ (Fail_C_FDConstr cd1 _)          (Fail_C_FDConstr cd2 _)          = compare cd1 cd2
compareConstr _ (Fail_C_FDConstr _ _)            _                                = LT
compareConstr _ _                                (Fail_C_FDConstr _ _)            = GT
compareConstr l (Guard_C_FDConstr cd1 _ x1)      (Guard_C_FDConstr cd2 _ x2)      = compare cd1 cd2 <<>> compareConstr l x1 x2

-- -----------------------------------------------------------------------------
-- Representation of FD domains
-- -----------------------------------------------------------------------------

data Domain = Range Int Int
  deriving (Eq, Ord, Show)

external_d_C_prim_FD_domain :: C_Int -> C_Int -> C_Int -> Cover
                         -> ConstStore -> Curry_Prelude.OP_List C_FDExpr
external_d_C_prim_FD_domain l u (Choices_C_Int _ (FreeID _ s) _) _ _ =
  if l' > u' then Curry_Prelude.OP_List else newFDVars s
  where l'           = fromCurry l
        u'           = fromCurry u
        dom          = Range l' u'
        newFDVars s' = let i   = getKey $ thisID $ leftSupply s'
                           s1 = rightSupply s'
                       in Curry_Prelude.OP_Cons (FDVar i dom) (newFDVars s1)

-- -----------------------------------------------------------------------------
-- Arithmetic FD constraints
-- -----------------------------------------------------------------------------

external_d_C_prim_fdc :: C_Int -> Cover -> ConstStore -> C_FDExpr
external_d_C_prim_fdc x@(Choices_C_Int _ _ _) _ _ =
  internalError $ "CLPFD2.fdc: Expected ground value but got " ++ (show x)
external_d_C_prim_fdc x                       _ _ = FDVal (fromCurry x)

external_d_C_prim_FD_plus :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                          -> C_FDExpr
external_d_C_prim_FD_plus (FDVal v1) (FDVal v2) _ _ = FDVal (v1 + v2)
external_d_C_prim_FD_plus e1         e2         _ _ = FDArith Plus e1 e2

external_d_C_prim_FD_minus :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                           -> C_FDExpr
external_d_C_prim_FD_minus (FDVal v1) (FDVal v2) _ _ = FDVal (v1 - v2)
external_d_C_prim_FD_minus e1         e2         _ _ = FDArith Minus e1 e2

external_d_C_prim_FD_mult :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                          -> C_FDExpr
external_d_C_prim_FD_mult (FDVal v1) (FDVal v2) _ _ = FDVal (v1 * v2)
external_d_C_prim_FD_mult e1         e2         _ _ = FDArith Mult e1 e2

external_d_C_prim_FD_div :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                         -> C_FDExpr
external_d_C_prim_FD_div (FDVal v1) (FDVal v2) _ _ = FDVal (v1 `div` v2)
external_d_C_prim_FD_div e1         e2         _ _ = FDArith Div e1 e2

external_d_C_prim_FD_mod :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                         -> C_FDExpr
external_d_C_prim_FD_mod (FDVal v1) (FDVal v2) _ _ = FDVal (v1 `mod` v2)
external_d_C_prim_FD_mod e1         e2         _ _ = FDArith Mod e1 e2

external_d_C_prim_FD_abs :: C_FDExpr -> Cover -> ConstStore -> C_FDExpr
external_d_C_prim_FD_abs (FDVal v) _ _ = FDVal (abs v)
external_d_C_prim_FD_abs e         _ _ = FDAbs e

external_d_C_prim_FD_channel :: C_FDConstr -> Cover -> ConstStore -> C_FDExpr
external_d_C_prim_FD_channel (FDConst False) _ _ = (FDVal 0)
external_d_C_prim_FD_channel (FDConst True)  _ _ = (FDVal 1)
external_d_C_prim_FD_channel c               _ _ = (FDChannel c)

-- -----------------------------------------------------------------------------
-- Relational FD constraints
-- -----------------------------------------------------------------------------

external_d_C_prim_FD_equal :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                           -> C_FDConstr
external_d_C_prim_FD_equal (FDVal v1) (FDVal v2) _ _ = FDConst (v1 == v2)
external_d_C_prim_FD_equal e1         e2         _ _ = FDRel Equal e1 e2

external_d_C_prim_FD_diff :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                          -> C_FDConstr
external_d_C_prim_FD_diff (FDVal v1) (FDVal v2) _ _ = FDConst (v1 /= v2)
external_d_C_prim_FD_diff e1         e2         _ _ = FDRel Diff e1 e2

external_d_C_prim_FD_less :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                          -> C_FDConstr
external_d_C_prim_FD_less (FDVal v1) (FDVal v2) _ _ = FDConst (v1 < v2)
external_d_C_prim_FD_less e1         e2         _ _ = FDRel Less e1 e2

external_d_C_prim_FD_lessEqual :: C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                               -> C_FDConstr
external_d_C_prim_FD_lessEqual (FDVal v1) (FDVal v2) _ _ = FDConst (v1 == v2)
external_d_C_prim_FD_lessEqual e1         e2         _ _ = FDRel LessEqual e1 e2

external_d_C_prim_FD_and :: C_FDConstr -> C_FDConstr -> Cover -> ConstStore
                         -> C_FDConstr
external_d_C_prim_FD_and (FDConst True)     c2                 _ _ = c2
external_d_C_prim_FD_and c1@(FDConst False) _                  _ _ = c1
external_d_C_prim_FD_and c1                 (FDConst True)     _ _ = c1
external_d_C_prim_FD_and c1                 c2@(FDConst False) _ _ = c2
external_d_C_prim_FD_and c1                 c2                 _ _ = FDAnd c1 c2

external_d_C_prim_FD_or :: C_FDConstr -> C_FDConstr -> Cover -> ConstStore
                        -> C_FDConstr
external_d_C_prim_FD_or c1@(FDConst True) _                 _ _ = c1
external_d_C_prim_FD_or (FDConst False)   c2                _ _ = c2
external_d_C_prim_FD_or _                 c2@(FDConst True) _ _ = c2
external_d_C_prim_FD_or c1                (FDConst False)   _ _ = c1
external_d_C_prim_FD_or c1                c2                _ _ = FDOr c1 c2

external_d_C_prim_FD_neg :: C_FDConstr -> Cover -> ConstStore -> C_FDConstr
external_d_C_prim_FD_neg (FDConst b) _ _ = FDConst (not b)
external_d_C_prim_FD_neg c           _ _ = FDNeg c

-- -----------------------------------------------------------------------------
-- Global FD constraints
-- -----------------------------------------------------------------------------

external_d_C_prim_FD_sum :: Curry_Prelude.OP_List C_FDExpr -> Cover -> ConstStore -> C_FDExpr
external_d_C_prim_FD_sum xs _ _ = FDSum (fromCurry xs)

external_d_C_prim_FD_allDifferent :: Curry_Prelude.OP_List C_FDExpr -> Cover -> ConstStore
                                  -> C_FDConstr
external_d_C_prim_FD_allDifferent xs _ _ = FDAllDifferent (fromCurry xs)

external_d_C_prim_FD_sorted :: Curry_Prelude.OP_List C_FDExpr -> Cover -> ConstStore
                            -> C_FDConstr
external_d_C_prim_FD_sorted xs _ _ = FDSorted (fromCurry xs)

-- -----------------------------------------------------------------------------
-- Access FD expression list
-- -----------------------------------------------------------------------------

external_d_C_prim_FD_at :: Curry_Prelude.OP_List C_FDExpr -> C_FDExpr -> Cover -> ConstStore
                        -> C_FDExpr
external_d_C_prim_FD_at xs e _ _ = FDAt (fromCurry xs) e

-- -----------------------------------------------------------------------------
-- Higher-order FD constraints
-- -----------------------------------------------------------------------------

external_d_C_prim_FD_loopall :: C_FDExpr -> C_FDExpr
                             -> (C_FDExpr -> Cover -> ConstStore -> C_FDConstr)
                             -> Cover -> ConstStore -> C_FDConstr
external_d_C_prim_FD_loopall from to constr cd cs
  = FDLoopAll from to (\e -> constr e cd cs)

external_nd_C_prim_FD_loopall :: C_FDExpr -> C_FDExpr
                              -> (Func C_FDExpr C_FDConstr) -> IDSupply -> Cover
                              -> ConstStore -> C_FDConstr
external_nd_C_prim_FD_loopall from to constr s cd cs
  = FDLoopAll from to (\e -> nd_apply constr e s cd cs)

external_d_C_prim_FD_forall :: Curry_Prelude.OP_List C_FDExpr
                            -> (C_FDExpr -> Cover -> ConstStore -> C_FDConstr)
                            -> Cover -> ConstStore -> C_FDConstr
external_d_C_prim_FD_forall xs constr cd cs
  = FDForAll (fromCurry xs) (\e -> constr e cd cs)

external_nd_C_prim_FD_forall :: Curry_Prelude.OP_List C_FDExpr
                              -> (Func C_FDExpr C_FDConstr) -> IDSupply -> Cover
                              -> ConstStore -> C_FDConstr
external_nd_C_prim_FD_forall xs constr s cd cs
  = FDForAll (fromCurry xs) (\e -> nd_apply constr e s cd cs)

-- -----------------------------------------------------------------------------
-- MCP solver translation
-- -----------------------------------------------------------------------------

-- translation monad
type TLM = S.State TLState

-- mapping of domains to FD variables
type VarMap = Map.Map Domain (Set.Set C_FDExpr)

-- translation state
-- stores all FD variables occurring during translation
-- with their corresponding domain
data TLState = TLState { varMap :: VarMap
                       , nextId :: FDIdent
                       }

-- initial translation state
initState :: TLState
initState = TLState { varMap = Map.empty
                    , nextId = -1
                    }

getVarMap :: TLM VarMap
getVarMap = S.gets varMap

getIdent :: TLM FDIdent
getIdent = S.gets nextId

setVarMap :: VarMap -> TLM ()
setVarMap vm = S.modify $ \s -> s { varMap = vm }

decIdent :: TLM ()
decIdent = S.modify $ \s -> s { nextId = (nextId s) - 1 }

-- get new FD parameter (for higher-order constraints)
newParam :: TLM C_FDExpr
newParam = do
  i <- getIdent
  decIdent
  return (FDParam i)

-- get a MCP collection of all FD variables
-- which were (so far) collected in the varMap during the translation process
getAllVars :: TLM [C_FDExpr]
getAllVars = do
  vm <- getVarMap
  let vars = (Set.elems . Set.unions . Map.elems) vm
  return vars

-- Translation of FD expressions into MCP terms
tlFDExpr :: C_FDExpr -> TLM ModelInt
tlFDExpr (FDVal v) = return (asExpr v)
tlFDExpr var@(FDVar i dom) = do
  vm <- getVarMap
  let i'  = fromInteger i
      mcpVar = asExpr (ModelIntVar i' :: ModelIntTerm ModelFunctions)
  setVarMap $ Map.insertWith Set.union dom (Set.singleton var) vm
  return mcpVar
tlFDExpr (FDParam i) = do
  let i'  = fromInteger i
      par = asExpr (ModelIntVar i' :: ModelIntTerm ModelFunctions)
  return par
tlFDExpr (FDAt xs e) = do
  xs' <- tlFDExprList xs
  e'  <- tlFDExpr e
  return (xs' ! e')
tlFDExpr (FDArith op e1 e2) = do
  e1' <- tlFDExpr e1
  e2' <- tlFDExpr e2
  return (e1' `op'` e2')
  where op' = tlArithOp op
        tlArithOp Plus  = (@+)
        tlArithOp Minus = (@-)
        tlArithOp Mult  = (@*)
        tlArithOp Div   = (@/)
        tlArithOp Mod   = (@%)
tlFDExpr (FDAbs e) = do
  e' <- tlFDExpr e
  return (abs e')
tlFDExpr (FDSum xs) = do
  xs' <- tlFDExprList xs
  return (xsum xs')
tlFDExpr (FDChannel c) = do
  c' <- tlFDConstr c
  return (channel c')
tlFDExpr e = internalError $ "CLPFD2.tlFDExpr: Unknown FD expression: " ++ show e

-- Translation of lists of FD expressions into MCP collections
tlFDExprList :: [C_FDExpr] -> TLM ModelCol
tlFDExprList xs = do
  xs' <- mapM tlFDExpr xs
  return (list xs')

-- Translation of FD constraints into MCP constraints
tlFDConstr :: C_FDConstr -> TLM Model
tlFDConstr (FDConst b) = return (toBoolExpr b)
tlFDConstr (FDRel op e1 e2) = do
  e1' <- tlFDExpr e1
  e2' <- tlFDExpr e2
  return (e1' `op'` e2')
  where op' = tlRelOp op
        tlRelOp Equal     = (@=)
        tlRelOp Diff      = (@/=)
        tlRelOp Less      = (@<)
        tlRelOp LessEqual = (@<=)
tlFDConstr (FDAllDifferent xs) = do
  xs' <- tlFDExprList xs
  return (allDiff xs')
tlFDConstr (FDSorted xs) = do
  xs' <- tlFDExprList xs
  return (sorted xs')
tlFDConstr (FDLoopAll from to constr) = do
  from'   <- tlFDExpr from
  to'     <- tlFDExpr to
  param   <- newParam   -- introduce new parameter of type C_FDExpr
  param'  <- tlFDExpr param
  constr' <- tlFDConstr (constr param)
  return (loopall (from', to') (\x -> ((x @= param') :: Model) @&& constr'))
tlFDConstr (FDForAll xs constr) = do
  xs'     <- tlFDExprList xs
  param   <- newParam
  param'  <- tlFDExpr param
  constr' <- tlFDConstr (constr param)
  return (forall xs' (\x -> ((x @= param') :: Model) @&& constr'))
tlFDConstr (FDAnd c1 c2) = do
  c1' <- tlFDConstr c1
  c2' <- tlFDConstr c2
  return (c1' @&& c2')
tlFDConstr (FDOr c1 c2) = do
  c1' <- tlFDConstr c1
  c2' <- tlFDConstr c2
  return (c1' @|| c2')
tlFDConstr (FDNeg c) = do
  c' <- tlFDConstr c
  return (inv c')
tlFDConstr c = internalError $ "CLPFD2.tlFDConstr: Unknown constraint: " ++ show c

-- -----------------------------------------------------------------------------
-- MCP solver solving
-- -----------------------------------------------------------------------------

type OvertonTree = Tree (FDInstance OvertonFD) ModelCol

type GecodeRuntimeTree
  = Tree (FDInstance (GecodeWrappedSolver RuntimeGecodeSolver)) ModelCol

type GecodeSearchTree
  = Tree (FDInstance (GecodeWrappedSolver SearchGecodeSolver)) ModelCol

genMCPModel :: FDSolver s => C_FDConstr -> [C_FDExpr]
            -> TLM (Tree (FDInstance s) ModelCol)
genMCPModel cs lvars = do
  mcpConstr <- tlFDConstr cs
  domConstr <- genDomConstr
  mcpLVars  <- getLabelVars lvars
  let model = domConstr @&& mcpConstr
  case mcpLVars of
    ColList [] -> return false
    _          -> return $ genModelTree model mcpLVars
  where
    getLabelVars :: [C_FDExpr] -> TLM ModelCol
    getLabelVars []   = getAllVars >>= tlFDExprList
    getLabelVars vars = tlFDExprList vars

    genModelTree :: FDSolver s => Model -> ModelCol
                 -> Tree (FDInstance s) ModelCol
    genModelTree (BoolConst True)  t = return t
    genModelTree (BoolConst False) _ = false
    genModelTree c                 t = (Left c) `addTo` (return t)

genDomConstr :: TLM Model
genDomConstr = do
  vm         <- getVarMap
  domConstrs <- mapM genDomConstr' $ Map.assocs vm
  return $ foldr (@&&) (BoolConst True) domConstrs
  where
    genDomConstr' ((Range l u), vars) = do
      col <- tlFDExprList (Set.elems vars)
      let dom = (asExpr l, asExpr u)
      return $ forall col (\v -> v @: dom)

external_d_C_prim_solveFD :: Curry_Prelude.OP_List C_Option -> C_FDConstr -> Cover -> ConstStore
                          -> Curry_Prelude.OP_List (Curry_Prelude.OP_List C_Int)
external_d_C_prim_solveFD opts constr _ _
  = let opts'     = getOpts $ fromCurry opts
        solutions = runSolver opts' constr []
    in toCurry solutions

external_d_C_prim_solveFDVars :: Curry_Prelude.OP_List C_Option -> C_FDConstr
                              -> Curry_Prelude.OP_List C_FDExpr -> Cover -> ConstStore
                              -> Curry_Prelude.OP_List (Curry_Prelude.OP_List C_Int)
external_d_C_prim_solveFDVars opts constr lvars _ _
  = let opts'     = getOpts $ fromCurry opts
        solutions = runSolver opts' constr (fromCurry lvars)
    in toCurry solutions

isSolver :: C_Option -> Bool
#ifdef GECODE
isSolver C_Overton       = True
isSolver C_GecodeRuntime = True
isSolver C_GecodeSearch  = True
isSolver _               = False
#else
isSolver _               = False
#endif

isLabel :: C_Option -> Bool
isLabel C_InOrder   = True
isLabel C_FirstFail = True
isLabel C_MiddleOut = True
isLabel C_EndsOut   = True
isLabel _           = False

isSearch :: C_Option -> Bool
isSearch C_DepthFirst   = True
isSearch C_BreadthFirst = True
isSearch _              = False

isTransformer :: C_Option -> Bool
isTransformer C_FirstSolution = True
isTransformer C_AllSolutions  = True
isTransformer _               = False

findWithDefault :: a -> (a -> Bool) -> [a] -> a
findWithDefault def _ [] = def
findWithDefault def p (x:xs) | p x       = x
                             | otherwise = findWithDefault def p xs

-- only the first given option of each kind is used
getOpts :: [C_Option] -> (C_Option, C_Option, C_Option, C_Option)
getOpts opts
  = let solverOpt = findWithDefault C_Overton isSolver opts
        labelOpt  = findWithDefault C_InOrder isLabel opts
        searchOpt = findWithDefault C_DepthFirst isSearch opts
        transOpt  = findWithDefault C_FirstSolution isTransformer opts
    in (solverOpt, searchOpt, transOpt,labelOpt)

-- Run a MCP solver with different search strategies and search transformers
runSolver :: (C_Option, C_Option, C_Option, C_Option) -> C_FDConstr
          -> [C_FDExpr] -> [[Int]]
runSolver (C_GecodeRuntime, C_DepthFirst, C_FirstSolution, labelOpt) constr labelVars
  = S.evalState (gecodeRuntime_DFS_FS constr labelVars labelOpt) initState
runSolver (C_GecodeRuntime, C_DepthFirst, C_AllSolutions, labelOpt) constr labelVars
  = S.evalState (gecodeRuntime_DFS_AS constr labelVars labelOpt) initState
runSolver (C_GecodeRuntime, C_BreadthFirst, C_FirstSolution, labelOpt) constr labelVars
  = S.evalState (gecodeRuntime_BFS_FS constr labelVars labelOpt) initState
runSolver (C_GecodeRuntime, C_BreadthFirst, C_AllSolutions, labelOpt) constr labelVars
  = S.evalState (gecodeRuntime_BFS_AS constr labelVars labelOpt) initState

runSolver (C_GecodeSearch, C_DepthFirst, C_FirstSolution, _) constr labelVars
  = S.evalState (gecodeSearch_DFS_FS constr labelVars) initState
runSolver (C_GecodeSearch, C_DepthFirst, C_AllSolutions, _) constr labelVars
  = S.evalState (gecodeSearch_DFS_AS constr labelVars) initState
runSolver (C_GecodeSearch, C_BreadthFirst, C_FirstSolution, _) constr labelVars
  = S.evalState (gecodeSearch_BFS_FS constr labelVars) initState
runSolver (C_GecodeSearch, C_BreadthFirst, C_AllSolutions, _) constr labelVars
  = S.evalState (gecodeSearch_BFS_AS constr labelVars) initState

runSolver (C_Overton, C_DepthFirst, C_FirstSolution, labelOpt) constr labelVars
  = S.evalState (overton_DFS_FS constr labelVars labelOpt) initState
runSolver (C_Overton, C_DepthFirst, C_AllSolutions, labelOpt) constr labelVars
  = S.evalState (overton_DFS_AS constr labelVars labelOpt) initState
runSolver (C_Overton, C_BreadthFirst, C_FirstSolution, labelOpt) constr labelVars
  = S.evalState (overton_BFS_FS constr labelVars labelOpt) initState
runSolver (C_Overton, C_BreadthFirst, C_AllSolutions, labelOpt) constr labelVars
  = S.evalState (overton_BFS_AS constr labelVars labelOpt) initState

-- MCP gecode runtime solver with various search strategies and search transformers
gecodeRuntime_DFS_FS :: C_FDConstr -> [C_FDExpr] -> C_Option -> TLM [[Int]]
gecodeRuntime_DFS_FS constr labelVars labelOpt = do
  model <- genMCPModel constr labelVars
  let values = snd $ MCP.solve dfs fs $
        (model :: GecodeRuntimeTree) >>= labelWith labelOpt
  return $ map (map fromInteger) values

gecodeRuntime_DFS_AS :: C_FDConstr -> [C_FDExpr] -> C_Option -> TLM [[Int]]
gecodeRuntime_DFS_AS constr labelVars labelOpt = do
  model <- genMCPModel constr labelVars
  let values = snd $ MCP.solve dfs it $
        (model :: GecodeRuntimeTree) >>= labelWith labelOpt
  return $ map (map fromInteger) values

gecodeRuntime_BFS_FS :: C_FDConstr -> [C_FDExpr] -> C_Option -> TLM [[Int]]
gecodeRuntime_BFS_FS constr labelVars labelOpt = do
  model <- genMCPModel constr labelVars
  let values = snd $ MCP.solve bfs fs $
        (model :: GecodeRuntimeTree) >>= labelWith labelOpt
  return $ map (map fromInteger) values

gecodeRuntime_BFS_AS :: C_FDConstr -> [C_FDExpr] -> C_Option -> TLM [[Int]]
gecodeRuntime_BFS_AS constr labelVars labelOpt = do
  model <- genMCPModel constr labelVars
  let values = snd $ MCP.solve bfs it $
        (model :: GecodeRuntimeTree) >>= labelWith labelOpt
  return $ map (map fromInteger) values

-- MCP gecode search solver with various search strategies and search transformers
gecodeSearch_DFS_FS :: C_FDConstr -> [C_FDExpr] -> TLM [[Int]]
gecodeSearch_DFS_FS constr labelVars = do
  model <- genMCPModel constr labelVars
  let values = snd $ MCP.solve dfs fs $ (model :: GecodeSearchTree)
        >>= (\x -> setSearchMinimize >> return x) >>= labelCol
  return $ map (map fromInteger) values

gecodeSearch_DFS_AS :: C_FDConstr -> [C_FDExpr] -> TLM [[Int]]
gecodeSearch_DFS_AS constr labelVars = do
  model <- genMCPModel constr labelVars
  let values = snd $ MCP.solve dfs it $ (model :: GecodeSearchTree)
        >>= (\x -> setSearchMinimize >> return x) >>= labelCol
  return $ map (map fromInteger) values

gecodeSearch_BFS_FS :: C_FDConstr -> [C_FDExpr] -> TLM [[Int]]
gecodeSearch_BFS_FS constr labelVars = do
  model <- genMCPModel constr labelVars
  let values = snd $ MCP.solve bfs fs $ (model :: GecodeSearchTree)
        >>= (\x -> setSearchMinimize >> return x) >>= labelCol
  return $ map (map fromInteger) values

gecodeSearch_BFS_AS :: C_FDConstr -> [C_FDExpr] -> TLM [[Int]]
gecodeSearch_BFS_AS constr labelVars = do
  model <- genMCPModel constr labelVars
  let values = snd $ MCP.solve bfs it $ (model :: GecodeSearchTree)
        >>= (\x -> setSearchMinimize >> return x) >>= labelCol
  return $ map (map fromInteger) values

-- MCP overton solver with various search strategies and search transformers
overton_DFS_FS :: C_FDConstr -> [C_FDExpr] -> C_Option -> TLM [[Int]]
overton_DFS_FS constr labelVars labelOpt = do
  model <- genMCPModel constr labelVars
  return $ snd $ MCP.solve dfs fs $
    (model :: OvertonTree) >>= labelWith labelOpt

overton_DFS_AS :: C_FDConstr -> [C_FDExpr] -> C_Option -> TLM [[Int]]
overton_DFS_AS constr labelVars labelOpt = do
  model <- genMCPModel constr labelVars
  return $ snd $ MCP.solve dfs it $
    (model :: OvertonTree) >>= labelWith labelOpt

overton_BFS_FS :: C_FDConstr -> [C_FDExpr] -> C_Option -> TLM [[Int]]
overton_BFS_FS constr labelVars labelOpt = do
  model <- genMCPModel constr labelVars
  return $ snd $ MCP.solve bfs fs $
    (model :: OvertonTree) >>= labelWith labelOpt

overton_BFS_AS :: C_FDConstr -> [C_FDExpr] -> C_Option -> TLM [[Int]]
overton_BFS_AS constr labelVars labelOpt = do
  model <- genMCPModel constr labelVars
  return $ snd $ MCP.solve bfs it $
    (model :: OvertonTree) >>= labelWith labelOpt

-- Label MCP collection with given strategy
labelWith :: (FDSolver s, MonadTree m, TreeSolver m ~ FDInstance s,
              EnumTerm s (FDIntTerm s)) => C_Option -> ModelCol
                                        -> m [TermBaseType s (FDIntTerm s)]
labelWith labelOpt (ColList l) = label $ do
  return $ do
    labelling (getLabelFunc labelOpt) l
    assignments l
  where getLabelFunc C_InOrder   = inOrder
        getLabelFunc C_FirstFail = firstFail
        getLabelFunc C_MiddleOut = middleOut
        getLabelFunc C_EndsOut   = endsOut
