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
  hlist  <- sy tree
  seqList hlist `seq` return $ hlist2clist hlist
 where
  seqList []     = ()
  seqList (x:xs) = seqList xs
external_d_C_getAllValues (Functions _ allValues _) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  list <- allValues tree
  return $ hlist2clist list

external_d_C_getLazyValues :: NormalForm a =>
                              C_Strategy a
                           -> a
                           -> Cover
                           -> ConstStore
                           -> CP.C_IO (CP.OP_List a)
external_d_C_getLazyValues (Strategy sy) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  hlist <- sy tree
  return $ hlist2clist hlist
external_d_C_getLazyValues (Functions _ _ lazyValues) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  hlist <- lazyValues tree
  return $ hlist2clist hlist

external_d_C_getOneValue :: NormalForm a =>
                            C_Strategy a
                         -> a
                         -> Cover
                         -> ConstStore
                         -> CP.C_IO (CP.C_Maybe a)
external_d_C_getOneValue (Strategy sy) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  hlist <- sy tree
  return $ hmaybe2cmaybe $ case hlist of
    []  -> Nothing
    x:_ -> Just x
external_d_C_getOneValue (Functions oneValue _ _) x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  mb <- oneValue tree
  return $ hmaybe2cmaybe mb

hmaybe2cmaybe Nothing  = CP.C_Nothing
hmaybe2cmaybe (Just a) = CP.C_Just a

hlist2clist [] = CP.OP_List
hlist2clist (x:xs) = CP.OP_Cons x $ hlist2clist xs

data C_Strategy a
    = Strategy  { getStrategy :: SearchTree a -> IO [a] }
    | Functions { getOneValue :: SearchTree a -> IO (Maybe a), getAllValues :: SearchTree a -> IO [a], getLazyValues :: SearchTree a -> IO [a] }

fromIOListStrategy s = Functions (\t -> s t >>= listIOToMaybe )
                                 (\t -> s t >>= evalIOList )
                                 (\t -> listIOToLazy $ s t)

external_d_C_parSearch :: Cover -> ConstStore -> C_Strategy a
external_d_C_parSearch _ _ = Strategy $ return . parSearch

external_d_C_fairSearch :: Cover -> ConstStore -> C_Strategy a
external_d_C_fairSearch _ _ = fromIOListStrategy fairSearch

external_d_C_conSearch :: CP.C_Int -> Cover -> ConstStore -> C_Strategy a
external_d_C_conSearch i _ _ = fromIOListStrategy (conSearch $ fromCurry i)

external_d_C_fairSearch' :: Cover -> ConstStore -> C_Strategy a
external_d_C_fairSearch' _ _ = fromIOListStrategy fairSearch'

external_d_C_fairSearch'' :: Cover -> ConstStore -> C_Strategy a
external_d_C_fairSearch'' _ _ = fromIOListStrategy fairSearch''

external_d_C_splitAll :: Cover -> ConstStore -> C_Strategy a
external_d_C_splitAll _ _ = Strategy $ return . splitAll

external_d_C_splitAll' :: Cover -> ConstStore -> C_Strategy a
external_d_C_splitAll' _ _ = Strategy $ return . splitAll'

external_d_C_splitLimitDepth :: CP.C_Int -> Cover -> ConstStore -> C_Strategy a
external_d_C_splitLimitDepth i _ _ = Strategy $ return . (splitLimitDepth $ fromCurry i)

external_d_C_splitAlternating :: CP.C_Int -> Cover -> ConstStore -> C_Strategy a
external_d_C_splitAlternating i _ _ = Strategy $ return . (splitAlternating $ fromCurry i)

external_d_C_splitPower :: Cover -> ConstStore -> C_Strategy a
external_d_C_splitPower _ _ = Strategy $ return . splitPower

external_d_C_bfsParallel :: Cover -> ConstStore -> C_Strategy a
external_d_C_bfsParallel _ _ = Strategy $ return . bfsParallel

external_d_C_bfsParallel' :: Cover -> ConstStore -> C_Strategy a
external_d_C_bfsParallel' _ _ = Strategy $ return . bfsParallel'

data C_SplitStrategy a
    = SplitStrategy { getSplit :: TaskBufferSTM b => Maybe (SplitFunction b a) }

external_d_C_dfsBag :: C_SplitStrategy a -> Cover -> ConstStore -> C_Strategy a
external_d_C_dfsBag split _ _ =
  let s  = flip $ dfsBag $ getSplit split
  in Functions (s getResult)
               (s getAllResults)
               (dfsBagLazy $ getSplit split)

external_d_C_fdfsBag :: C_SplitStrategy a -> Cover -> ConstStore -> C_Strategy a
external_d_C_fdfsBag split _ _ =
  let s = flip $ fdfsBag $ getSplit split
  in Functions (s getResult)
               (s getAllResults)
               (fdfsBagLazy $ getSplit split)

external_d_C_bfsBag :: C_SplitStrategy a -> Cover -> ConstStore -> C_Strategy a
external_d_C_bfsBag split _ _ =
  let s = flip $ bfsBag $ getSplit split
  in Functions (s getResult)
               (s getAllResults)
               (bfsBagLazy $ getSplit split)

external_d_C_fairBag :: C_SplitStrategy a -> Cover -> ConstStore -> C_Strategy a
external_d_C_fairBag split _ _ =
  let s = flip $ fairBag $ getSplit split
  in Functions (s getResult)
               (s getAllResults)
               (fairBagLazy $ getSplit split)

external_d_C_commonBuffer :: Cover -> ConstStore -> C_SplitStrategy a
external_d_C_commonBuffer _ _ = SplitStrategy Nothing

external_d_C_takeFirst :: Cover -> ConstStore -> C_SplitStrategy a
external_d_C_takeFirst _ _ = SplitStrategy $ Just takeFirst

external_d_C_splitVertical :: Cover -> ConstStore -> C_SplitStrategy a
external_d_C_splitVertical _ _ = SplitStrategy $ Just splitVertical

external_d_C_splitHalf :: Cover -> ConstStore -> C_SplitStrategy a
external_d_C_splitHalf _ _ = SplitStrategy $ Just splitHalf
