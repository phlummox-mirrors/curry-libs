{-# LANGUAGE Rank2Types #-}
import Control.Monad.SearchTree
import Control.Monad
import MonadSearch
import MonadList
import Strategies
import Control.Parallel.Strategies
import Control.Concurrent.Bag.Safe (SplitFunction, TaskBufferSTM (..), takeFirst)
import qualified Curry_Prelude as CP

external_d_C_getAllValues :: NormalForm a =>
                             C_Strategy a
                          -> a 
                          -> Cover
                          -> ConstStore
                          -> CP.C_IO (CP.OP_List a)
external_d_C_getAllValues (Strategy sy) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  list  <- sy tree
  hlist <- evalIOList list
  return $ hlist2clist hlist
external_d_C_getAllValues (Functions _ allValues) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  list <- allValues tree
  return $ hlist2clist list

external_d_C_getOneValue :: NormalForm a =>
                            C_Strategy a
                         -> a
                         -> Cover
                         -> ConstStore
                         -> CP.C_IO (CP.C_Maybe a)
external_d_C_getOneValue (Strategy sy) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  list <- sy tree
  liftM hmaybe2cmaybe $ listIOToMaybe list
external_d_C_getOneValue (Functions oneValue _) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  mb <- oneValue tree
  return $ hmaybe2cmaybe mb

hmaybe2cmaybe Nothing  = CP.C_Nothing
hmaybe2cmaybe (Just a) = CP.C_Just a

hlist2clist [] = CP.OP_List
hlist2clist (x:xs) = CP.OP_Cons x $ hlist2clist xs

data C_Strategy a
    = Strategy  { getStrategy :: SearchTree a -> IO (IOList a) }
    | Functions { getOneValue :: SearchTree a -> IO (Maybe a), getAllValues :: SearchTree a -> IO [a] }

external_d_C_parSearch :: Cover -> ConstStore -> C_Strategy a
external_d_C_parSearch _ _ = Strategy (fromList . parSearch)

external_d_C_fairSearch :: Cover -> ConstStore -> C_Strategy a
external_d_C_fairSearch _ _ = Strategy fairSearch

external_d_C_conSearch :: CP.C_Int -> Cover -> ConstStore -> C_Strategy a
external_d_C_conSearch i _ _ = Strategy $ conSearch $ fromCurry i

external_d_C_splitAll :: Cover -> ConstStore -> C_Strategy a
external_d_C_splitAll _ _ = Strategy $ fromList . splitAll

external_d_C_splitLimitDepth :: CP.C_Int -> Cover -> ConstStore -> C_Strategy a
external_d_C_splitLimitDepth i _ _ = Strategy $ fromList . (splitLimitDepth $ fromCurry i)

external_d_C_splitAlternating :: CP.C_Int -> Cover -> ConstStore -> C_Strategy a
external_d_C_splitAlternating i _ _ = Strategy $ fromList . (splitAlternating $ fromCurry i)

external_d_C_splitPower :: Cover -> ConstStore -> C_Strategy a
external_d_C_splitPower _ _ = Strategy $ fromList . splitPower

external_d_C_bfsParallel :: Cover -> ConstStore -> C_Strategy a
external_d_C_bfsParallel _ _ = Strategy $ fromList . bfsParallel

data C_SplitStrategy a
    = SplitStrategy { getSplit :: TaskBufferSTM b => Maybe (SplitFunction b a) }

external_d_C_dfsBag :: C_SplitStrategy a -> Cover -> ConstStore -> C_Strategy a
external_d_C_dfsBag split _ _ = let s = flip $ dfsBag $ getSplit split in Functions (s getResult) (s getAllResults)

external_d_C_fdfsBag :: C_SplitStrategy a -> Cover -> ConstStore -> C_Strategy a
external_d_C_fdfsBag split _ _ = let s = flip $ fdfsBag $ getSplit split in Functions (s getResult) (s getAllResults)

external_d_C_bfsBag :: C_SplitStrategy a -> Cover -> ConstStore -> C_Strategy a
external_d_C_bfsBag split _ _ = let s = flip $ bfsBag $ getSplit split in Functions (s getResult) (s getAllResults)

external_d_C_commonBuffer :: Cover -> ConstStore -> C_SplitStrategy a
external_d_C_commonBuffer _ _ = SplitStrategy Nothing

external_d_C_takeFirst :: Cover -> ConstStore -> C_SplitStrategy a
external_d_C_takeFirst _ _ = SplitStrategy $ Just takeFirst

external_d_C_splitVertical :: Cover -> ConstStore -> C_SplitStrategy a
external_d_C_splitVertical _ _ = SplitStrategy $ Just splitVertical

external_d_C_splitHalf :: Cover -> ConstStore -> C_SplitStrategy a
external_d_C_splitHalf _ _ = SplitStrategy $ Just splitHalf
