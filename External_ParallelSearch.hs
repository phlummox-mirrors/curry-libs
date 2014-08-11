{-# LANGUAGE Rank2Types #-}
import Control.Monad.SearchTree
import Control.Monad
import MonadSearch
import MonadList
import Strategies
import Control.Parallel.Strategies
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

external_d_C_fairSearch :: Cover -> ConstStore -> C_Strategy a
external_d_C_fairSearch _ _ = Strategy fairSearch

external_d_C_conSearch :: CP.C_Int -> Cover -> ConstStore -> C_Strategy a
external_d_C_conSearch i _ _ = Strategy (conSearch $ fromCurry i)

external_d_C_splitAll :: Cover -> ConstStore -> C_Strategy a
external_d_C_splitAll _ _ = Strategy $ return . splitAll

external_d_C_bfsParallel :: Cover -> ConstStore -> C_Strategy a
external_d_C_bfsParallel _ _ = Strategy $ return . bfsParallel

external_d_C_dfsBag :: Cover -> ConstStore -> C_Strategy a
external_d_C_dfsBag _ _ =
  let s  = flip $ dfsBag
  in Functions (s getResult)
               (s getAllResults)
               dfsBagLazy

external_d_C_fdfsBag :: Cover -> ConstStore -> C_Strategy a
external_d_C_fdfsBag _ _ =
  let s = flip $ fdfsBag
  in Functions (s getResult)
               (s getAllResults)
               fdfsBagLazy

external_d_C_bfsBag :: Cover -> ConstStore -> C_Strategy a
external_d_C_bfsBag _ _ =
  let s = flip $ bfsBag
  in Functions (s getResult)
               (s getAllResults)
               bfsBagLazy

external_d_C_fairBag :: Cover -> ConstStore -> C_Strategy a
external_d_C_fairBag _ _ =
  let s = flip $ fairBag
  in Functions (s getResult)
               (s getAllResults)
               fairBagLazy
