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
external_d_C_getAllValues sy x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  list  <- getStrategy sy tree
  hlist <- evalIOList list
  return $ hlist2clist hlist
 where
  hlist2clist [] = CP.OP_List
  hlist2clist (x:xs) = CP.OP_Cons x $ hlist2clist xs

external_d_C_getOneValue :: NormalForm a =>
                            C_Strategy a
                         -> a
                         -> Cover
                         -> ConstStore
                         -> CP.C_IO (CP.C_Maybe a)
external_d_C_getOneValue sy x c s = fromIO $ do
  let tree = encapsulatedSearch x c s
  list <- getStrategy sy tree
  liftM hmaybe2cmaybe $ listIOToMaybe list
 where
  hmaybe2cmaybe Nothing  = CP.C_Nothing
  hmaybe2cmaybe (Just a) = CP.C_Just a

data C_Strategy a
    = Strategy { getStrategy :: SearchTree a -> IO (IOList a) }

external_d_C_parSearch :: Cover -> ConstStore -> C_Strategy a
external_d_C_parSearch _ _ = Strategy (fromList . parSearch)

external_d_C_evalSearch :: Cover -> ConstStore -> C_Strategy a
external_d_C_evalSearch _ _ = Strategy (fromList . evalSearch)

external_d_C_fairSearch :: Cover -> ConstStore -> C_Strategy a
external_d_C_fairSearch _ _ = Strategy fairSearch

external_d_C_conSearch :: CP.C_Int -> Cover -> ConstStore -> C_Strategy a
external_d_C_conSearch i _ _ = Strategy $ conSearch $ fromCurry i
