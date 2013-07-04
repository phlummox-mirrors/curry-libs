import qualified Curry_Prelude as CP

import FDData
import PrimTypes

external_d_C_prim_neg :: CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Int
external_d_C_prim_neg b result _
  | isFree b  = guardCons defCover (WrappedConstr [c]) result
  | otherwise = toCurry (((fromCurry b) + 1) `mod` 2 :: Int)
 where
  c = wrapCs $ BNeg (toCsExpr b) (toCsExpr result)

external_d_C_prim_and :: CP.C_Int -> CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Int
external_d_C_prim_and b1 b2 result cs
  | isFree b1 || isFree b2  = guardCons defCover (WrappedConstr [c]) result
  | otherwise               = CP.d_OP_star b1 b2 cs
 where
  c = wrapCs $ newRelConstr Conjunction b1 b2 result

external_d_C_prim_or :: CP.C_Int -> CP.C_Int -> CP.C_Int -> ConstStore -> CP.C_Int
external_d_C_prim_or b1 b2 result _
  | isFree b1 || isFree b2  = guardCons defCover (WrappedConstr [c]) result
  | otherwise               = toCurry (((fromCurry b1) + (fromCurry b2)) `mod` 2 :: Int)
 where
  c = wrapCs $ newRelConstr Disjunction b1 b2 result

external_d_C_prim_sat :: CP.C_Int -> CP.C_Int -> ConstStore -> C_Success
external_d_C_prim_sat b (CP.Choices_C_Int _ i _) _ = guardCons defCover (WrappedConstr [c]) C_Success
 where
  c = wrapCs $ BLabel (toCsExpr b) i

newRelConstr :: Junctor -> CP.C_Int -> CP.C_Int -> CP.C_Int -> BConstraint
newRelConstr junctor b1 b2 result = BRel junctor (toCsExpr b1) (toCsExpr b2) (toCsExpr result)
