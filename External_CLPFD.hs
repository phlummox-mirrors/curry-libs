{-# LANGUAGE MultiParamTypeClasses #-}

import qualified Curry_Prelude as CP

import FDData

-- External implementations for constraint functions:
-- (curry list arguments have to be converted to haskell lists using toFDList)

external_d_C_prim_domain :: CP.OP_List CP.C_Int -> CP.C_Int -> CP.C_Int -> CP.OP_List CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_domain vs@(CP.Choices_OP_List _ i@(FreeID _ _) _) l u _ cs = ((\vs1 _ -> domain vs1 l u i) $!! (CP.d_C_ensureSpine vs cs)) cs
external_d_C_prim_domain vs l u (CP.Choices_OP_List _ i@(FreeID _ _) _) cs = ((\vs1 _ -> domain vs1 l u i) $!! (CP.d_C_ensureSpine vs cs)) cs

domain :: CP.OP_List CP.C_Int -> CP.C_Int -> CP.C_Int -> ID -> CP.C_Success
domain vs l u i =
  let c = wrapCs $ FDDomain (toFDList i vs) (toCsExpr l) (toCsExpr u)
  in guardCons defCover (WrappedConstr [c]) C_Success

external_d_C_prim_FD_plus :: CP.C_Int -> CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Int
external_d_C_prim_FD_plus x y res cs
  | isFree x || isFree y = guardCons defCover (WrappedConstr [c]) res
  | otherwise            = CP.d_OP_plus x y cs
 where
  c = wrapCs $ newArithConstr Plus x y res

external_d_C_prim_FD_minus :: CP.C_Int -> CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Int
external_d_C_prim_FD_minus x y res cs
  | isFree x || isFree y = guardCons defCover (WrappedConstr [c]) res
  | otherwise            = CP.d_OP_minus x y cs
 where
  c = wrapCs $ newArithConstr Minus x y res

external_d_C_prim_FD_times :: CP.C_Int -> CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Int
external_d_C_prim_FD_times x y res cs
  | isFree x || isFree y = guardCons defCover (WrappedConstr [c]) res 
  | otherwise            = CP.d_OP_star x y cs
 where
  c = wrapCs $ newArithConstr Mult x y res

external_d_C_prim_FD_equal :: CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_FD_equal x y cs
  | isFree x || isFree y = guardCons defCover (WrappedConstr [c]) C_Success
  | xEqualY              = C_Success
  | otherwise            = CP.d_C_failed cs
 where 
  xEqualY = fromCurry $ CP.d_OP_eq_eq x y cs
  c       = wrapCs $ newRelConstr Equal x y

external_d_C_prim_FD_notequal :: CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_FD_notequal x y cs
  | isFree x || isFree y = guardCons defCover (WrappedConstr [c]) C_Success
  | xNotEqualY           = C_Success
  | otherwise            = CP.d_C_failed cs
 where
  xNotEqualY = fromCurry $ CP.d_C_not (CP.d_OP_eq_eq x y cs) cs
  c          = wrapCs $ newRelConstr Diff x y

external_d_C_prim_FD_le :: CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_FD_le x y cs
  | isFree x || isFree y = guardCons defCover (WrappedConstr [c]) C_Success
  | xLessY               = C_Success
  | otherwise            = CP.d_C_failed cs
 where 
  xLessY = fromCurry $ CP.d_OP_lt_eq x (CP.d_OP_minus y (CP.C_Int 1#) cs) cs
  c      = wrapCs $ newRelConstr Less x y

external_d_C_prim_FD_leq :: CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_FD_leq x y cs
  | isFree x || isFree y = guardCons defCover (WrappedConstr [c]) C_Success
  | xLessEqualY          = C_Success
  | otherwise            = CP.d_C_failed cs
 where 
  xLessEqualY = fromCurry $ CP.d_OP_lt_eq x y cs
  c           = wrapCs $ newRelConstr LessEqual x y

external_d_C_prim_FD_ge :: CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_FD_ge x y cs = d_C_prim_FD_le y x cs

external_d_C_prim_FD_geq :: CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_FD_geq x y cs = d_C_prim_FD_leq y x cs

external_d_C_prim_allDifferent :: CP.OP_List CP.C_Int -> CP.OP_List CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_allDifferent vs@(CP.Choices_OP_List _ i@(FreeID _ _) _) _ cs = ((\vs1 cs1 -> allDifferent vs1 i cs1) $!! (CP.d_C_ensureSpine vs cs)) cs
external_d_C_prim_allDifferent vs (CP.Choices_OP_List _ i@(FreeID _ _) _) cs = ((\vs1 cs1 -> allDifferent vs1 i cs1) $!! (CP.d_C_ensureSpine vs cs)) cs

allDifferent :: CP.OP_List CP.C_Int -> ID -> ConstStore -> CP.C_Success
allDifferent vs i cs 
  | isFree vs || any isFree hvs = guardCons defCover (WrappedConstr [c]) C_Success
  | allDiff (fromCurry vs)      = C_Success
  | otherwise                   = CP.d_C_failed cs
 where
  hvs = toHaskellList id vs
  c   = wrapCs $ FDAllDifferent (toFDList i vs)

allDiff :: [Int] -> Bool
allDiff []     = True
allDiff (v:vs) = all (/= v) vs && allDiff vs

external_d_C_prim_sum :: CP.OP_List CP.C_Int -> CP.C_Int -> CP.OP_List CP.C_Int -> ConstStore -> CP.C_Int
external_d_C_prim_sum vs@(CP.Choices_OP_List _ i@(FreeID _ _) _) res _ cs = ((\vs1 _ -> sumList vs1 res i) $!! (CP.d_C_ensureSpine vs cs)) cs
external_d_C_prim_sum vs res (CP.Choices_OP_List _ i@(FreeID _ _) _) cs = ((\vs1 _ -> sumList vs1 res i) $!! (CP.d_C_ensureSpine vs cs)) cs

sumList :: CP.OP_List CP.C_Int -> CP.C_Int -> ID -> CP.C_Int
sumList vs res i
  | isFree vs || any isFree hvs = guardCons defCover (WrappedConstr [c]) res
  | otherwise                   = toCurry (Prelude.sum (fromCurry vs :: [Int]))
 where
  hvs = toHaskellList id vs
  c   = wrapCs $ FDSum (toFDList i vs) (toCsExpr res)

external_d_C_prim_labelingWith :: C_LabelingStrategy -> CP.OP_List CP.C_Int -> CP.OP_List CP.C_Int -> CP.OP_List CP.C_Int -> ConstStore -> CP.C_Success
external_d_C_prim_labelingWith strategy vs@(CP.Choices_OP_List _ i@(FreeID _ _) _) _ (CP.Choices_OP_List _ j@(FreeID _ _) _) cs = ((\vs1 _ -> labeling strategy vs1 j i) $!! (CP.d_C_ensureSpine vs cs)) cs
external_d_C_prim_labelingWith strategy vs (CP.Choices_OP_List _ i@(FreeID _ _) _) (CP.Choices_OP_List _ j@(FreeID _ _) _) cs = ((\vs1 _ -> labeling strategy vs1 j i) $!! (CP.d_C_ensureSpine vs cs)) cs

labeling :: C_LabelingStrategy -> CP.OP_List CP.C_Int -> ID -> ID -> CP.C_Success
labeling strategy vs j i = guardCons defCover (WrappedConstr [c]) C_Success
 where
  c = wrapCs $ FDLabeling (fromCurry strategy) (toFDList i vs) j

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
toFDList :: Constrainable a b => ID -> CP.OP_List a -> FDList b
toFDList i vs = FDList i (toHaskellList toCsExpr vs)
