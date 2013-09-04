{-# LANGUAGE MultiParamTypeClasses #-}

import qualified Curry_Prelude as CP
import Curry_List (d_C_sum)

import Solver.Constraints
import Solver.MCPUtils (allDifferent)

-- External implementations for constraint functions:
-- (curry list arguments have to be converted to haskell lists using toFDList)

-- yields Success or failed depending on whether given arguments satisfy the given predicate or not
cond :: NonDet a => (a -> a -> Cover -> ConstStore -> CP.C_Bool) -> a -> a -> Cover -> ConstStore -> C_Success
cond p x y cd cs
  | fromCurry (p x y cd cs) = C_Success
  | otherwise               = CP.d_C_failed cd cs

external_d_C_prim_domain :: CP.OP_List CP.C_Int -> CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_domain vs l u cd cs = narrowIfFree2 l u cont cont cd cs
 where 
  cont l' u' cd' _ = mkGuardExt cd' [wrapCs (FDDomain (toFDList vs) (toCsExpr l') (toCsExpr u'))] C_Success

external_d_C_prim_FD_plus :: CP.C_Int -> CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Int
external_d_C_prim_FD_plus x y result cd cs = narrowIfFree2 x y contFree CP.d_OP_plus cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newArithConstr Plus x' y' result)] result

external_d_C_prim_FD_minus :: CP.C_Int -> CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Int
external_d_C_prim_FD_minus x y result cd cs = narrowIfFree2 x y contFree CP.d_OP_minus cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newArithConstr Minus x' y' result)] result

external_d_C_prim_FD_times :: CP.C_Int -> CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Int
external_d_C_prim_FD_times x y result cd cs = narrowIfFree2 x y contFree CP.d_OP_star cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newArithConstr Mult x' y' result)] result

external_d_C_prim_FD_equal :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_FD_equal x y cd cs = narrowIfFree2 x y contFree (cond CP.d_OP_eq_eq) cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr Equal x' y')] C_Success

external_d_C_prim_FD_notequal :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_FD_notequal x y cd cs = narrowIfFree2 x y contFree (cond (\x' y' cd' cs' -> CP.d_C_not (CP.d_OP_eq_eq x' y' cd' cs') cd' cs')) cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr Diff x' y')] C_Success

external_d_C_prim_FD_le :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_FD_le x y cd cs = narrowIfFree2 x y contFree (cond (\x' y' cd' cs' -> CP.d_OP_lt_eq x' (CP.d_OP_minus y' (CP.C_Int 1#) cd' cs') cd' cs')) cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr Less x' y')] C_Success

external_d_C_prim_FD_leq :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_FD_leq x y cd cs = narrowIfFree2 x y contFree (cond CP.d_OP_lt_eq) cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr LessEqual x' y')] C_Success

external_d_C_prim_FD_ge :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_FD_ge x y cd cs = d_C_prim_FD_le y x cd cs

external_d_C_prim_FD_geq :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_FD_geq x y cd cs = d_C_prim_FD_leq y x cd cs

external_d_C_prim_allDifferent :: CP.OP_List CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_allDifferent vs cd cs
  | any isFree hvs                       = mkGuardExt cd [wrapCs (FDAllDifferent (toFDList vs))] C_Success
  | allDifferent (fromCurry vs :: [Int]) = C_Success
  | otherwise                            = CP.d_C_failed cd cs
 where
  hvs = toHaskellList id vs

external_d_C_prim_sum :: CP.OP_List CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Int
external_d_C_prim_sum vs result cd cs 
  | any isFree hvs = mkGuardExt cd [wrapCs (FDSum (toFDList vs) (toCsExpr result))] result
  | otherwise      = d_C_sum vs cd cs
 where
  hvs = toHaskellList id vs

external_d_C_prim_labelingWith :: C_LabelingStrategy -> CP.OP_List CP.C_Int -> CP.OP_List CP.C_Int -> Cover -> ConstStore -> CP.C_Success
external_d_C_prim_labelingWith _ CP.OP_List _ cd cs = CP.d_C_failed cd cs
external_d_C_prim_labelingWith strategy vs (CP.Choices_OP_List _ j@(FreeID _ _) _) cd cs =
  mkGuardExt cd [wrapCs (FDLabeling (fromCurry strategy) (toFDList vs) j)] C_Success

newArithConstr :: ArithOp -> CP.C_Int -> CP.C_Int -> CP.C_Int -> FDConstraint
newArithConstr arithOp x y result = FDArith arithOp (toCsExpr x) (toCsExpr y) (toCsExpr result)

newRelConstr :: RelOp -> CP.C_Int -> CP.C_Int -> FDConstraint
newRelConstr relOp x y = FDRel relOp (toCsExpr x) (toCsExpr y)

-- Conversion between Curry-LabelingStrategy and Haskell-LabelingStrategy

instance ConvertCurryHaskell C_LabelingStrategy LabelingStrategy where
  toCurry InOrder   = C_InOrder
  toCurry FirstFail = C_FirstFail
  toCurry MiddleOut = C_MiddleOut
  toCurry EndsOut   = C_EndsOut

  fromCurry C_InOrder   = InOrder
  fromCurry C_FirstFail = FirstFail
  fromCurry C_MiddleOut = MiddleOut
  fromCurry C_EndsOut   = EndsOut
  fromCurry _           = error "KiCS2 error: LabelingStrategy data with no ground term"

-- Convert to haskell list by converting list elements with given function
toHaskellList :: (a -> b) -> CP.OP_List a -> [b]
toHaskellList _ CP.OP_List        = []
toHaskellList f (CP.OP_Cons x xs) = f x : toHaskellList f xs

-- helper function to convert curry integer lists to lists of fd terms
toFDList :: Constrainable a b => CP.OP_List a -> [b]
toFDList = toHaskellList toCsExpr
