import qualified Curry_Prelude as CP

import Solver.Constraints

external_d_C_prim_neg :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Int
external_d_C_prim_neg b result cd cs = narrowIfFree b contFree contVal cd cs
 where
  contFree b'  cd'  _    = mkGuardExt cd' [wrapCs (BNeg (toCsExpr b') (toCsExpr result))] result
  contVal  b'' cd'' cs'' = CP.d_C_mod (CP.d_OP_plus b'' (CP.C_Int 1#) cd'' cs'') (CP.C_Int 2#) cd'' cs''

external_d_C_prim_and :: CP.C_Int -> CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Int
external_d_C_prim_and b1 b2 result cd cs = narrowIfFree2 b1 b2 contFree CP.d_OP_star cd cs
 where
  contFree b1' b2' cd' _ = mkGuardExt cd' [wrapCs (newRelConstr Conjunction b1' b2' result)] result

external_d_C_prim_or :: CP.C_Int -> CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> CP.C_Int
external_d_C_prim_or b1 b2 result cd cs = narrowIfFree2 b1 b2 contFree contVal cd cs
 where
  contFree b1'  b2'  cd' _ = mkGuardExt cd' [wrapCs (newRelConstr Disjunction b1' b2' result)] result
  contVal  b1'' b2'' _   _ = toCurry (intOr (fromCurry b1'') (fromCurry b2''))

intOr :: Int -> Int -> Int
intOr 1 _ = 1
intOr 0 x = x

external_d_C_prim_sat :: CP.C_Int -> CP.C_Int -> Cover -> ConstStore -> C_Success
external_d_C_prim_sat b (CP.Choices_C_Int _ i _) cd cs = narrowIfFree b contFree contFree cd cs
 where
  contFree b' cd' _ = mkGuardExt cd' [wrapCs (BLabel (toCsExpr b') i)] C_Success

newRelConstr :: Junctor -> CP.C_Int -> CP.C_Int -> CP.C_Int -> BConstraint
newRelConstr junctor b1 b2 result = BRel junctor (toCsExpr b1) (toCsExpr b2) (toCsExpr result)
