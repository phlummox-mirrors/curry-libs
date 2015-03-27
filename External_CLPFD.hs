{-# LANGUAGE MultiParamTypeClasses #-}

import Curry_List (d_C_sum)

import Solver.Constraints

-- External implementations for constraint functions:
-- (curry list arguments have to be converted to haskell lists using toFDList)

-- yields Success or failed depending on whether given arguments satisfy the given predicate or not
cond :: NonDet a => (a -> a -> Cover -> ConstStore -> Curry_Prelude.C_Bool) -> a -> a -> Cover -> ConstStore -> C_Success
cond p x y cd cs
  | fromCurry (p x y cd cs) = C_Success
  | otherwise               = Curry_Prelude.d_C_failed cd cs

external_d_C_prim_domain :: Curry_Prelude.OP_List Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_domain vs l u cd cs = narrowIfFree2 l u cont cont cd cs
 where 
  cont l' u' cd' _ = mkGuardExt cd' [wrapCs (FDDomain (toFDList vs) (toCsExpr l') (toCsExpr u'))] C_Success

external_d_C_prim_FD_plus :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Int
external_d_C_prim_FD_plus x y result cd cs = narrowIfFree2 x y contFree Curry_Prelude.d_OP_plus cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newArithConstr Plus x' y' result)] result

external_d_C_prim_FD_minus :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Int
external_d_C_prim_FD_minus x y result cd cs = narrowIfFree2 x y contFree Curry_Prelude.d_OP_minus cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newArithConstr Minus x' y' result)] result

external_d_C_prim_FD_times :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Int
external_d_C_prim_FD_times x y result cd cs = narrowIfFree2 x y contFree Curry_Prelude.d_OP_star cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newArithConstr Mult x' y' result)] result

external_d_C_prim_FD_equal :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_FD_equal x y cd cs = narrowIfFree2 x y contFree (cond Curry_Prelude.d_OP_eq_eq) cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr Equal x' y')] C_Success

external_d_C_prim_FD_notequal :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_FD_notequal x y cd cs = narrowIfFree2 x y contFree (cond (\x' y' cd' cs' -> Curry_Prelude.d_C_not (Curry_Prelude.d_OP_eq_eq x' y' cd' cs') cd' cs')) cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr Diff x' y')] C_Success

external_d_C_prim_FD_le :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_FD_le x y cd cs = narrowIfFree2 x y contFree (cond (\x' y' cd' cs' -> Curry_Prelude.d_OP_lt_eq x' (Curry_Prelude.d_OP_minus y' (Curry_Prelude.C_Int 1#) cd' cs') cd' cs')) cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr Less x' y')] C_Success

external_d_C_prim_FD_leq :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_FD_leq x y cd cs = narrowIfFree2 x y contFree (cond Curry_Prelude.d_OP_lt_eq) cd cs
 where
  contFree x' y' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr LessEqual x' y')] C_Success

external_d_C_prim_FD_ge :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_FD_ge x y cd cs = d_C_prim_FD_le y x cd cs

external_d_C_prim_FD_geq :: Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_FD_geq x y cd cs = d_C_prim_FD_leq y x cd cs

external_d_C_prim_allDifferent :: Curry_Prelude.OP_List Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_allDifferent vs cd cs
  | any isFree hvs                       = mkGuardExt cd [wrapCs (FDAllDifferent (toFDList vs))] C_Success
  | allDifferent (fromCurry vs :: [Int]) = C_Success
  | otherwise                            = Curry_Prelude.d_C_failed cd cs
 where
  hvs = toHaskellList id vs

external_d_C_prim_sum :: Curry_Prelude.OP_List Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Int
external_d_C_prim_sum vs result cd cs = mkGuardExt cd [wrapCs (FDSum (toFDList vs) (toCsExpr result))] result

-- external_d_C_prim_sum :: Curry_Prelude.OP_List Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Int
-- external_d_C_prim_sum vs result cd cs 
--   | any isFree hvs = mkGuardExt cd [wrapCs (FDSum (toFDList vs) (toCsExpr result))] result
--   | otherwise      = d_C_sum vs cd cs
--  where
--   hvs = toHaskellList id vs

external_d_C_prim_labelingWith :: C_LabelingStrategy -> Curry_Prelude.OP_List Curry_Prelude.C_Int -> Curry_Prelude.OP_List Curry_Prelude.C_Int -> Cover -> ConstStore -> Curry_Prelude.C_Success
external_d_C_prim_labelingWith _ Curry_Prelude.OP_List _ cd cs = Curry_Prelude.d_C_failed cd cs
external_d_C_prim_labelingWith strategy vs (Curry_Prelude.Choices_OP_List _ j@(FreeID _ _) _) cd cs =
  mkGuardExt cd [wrapCs (FDLabeling (fromCurry strategy) (toFDList vs) j)] C_Success

newArithConstr :: ArithOp -> Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> FDConstraint
newArithConstr arithOp x y result = FDArith arithOp (toCsExpr x) (toCsExpr y) (toCsExpr result)

newRelConstr :: RelOp -> Curry_Prelude.C_Int -> Curry_Prelude.C_Int -> FDConstraint
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
toHaskellList :: (a -> b) -> Curry_Prelude.OP_List a -> [b]
toHaskellList _ Curry_Prelude.OP_List        = []
toHaskellList f (Curry_Prelude.OP_Cons x xs) = f x : toHaskellList f xs

-- helper function to convert curry integer lists to lists of fd terms
toFDList :: Constrainable a b => Curry_Prelude.OP_List a -> [b]
toFDList = toHaskellList toCsExpr
