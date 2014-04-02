import Control.Monad
import Control.Applicative
import MonadSearch
import GHC.Exts (Int (I#))
import Strategies
import qualified Curry_ValueSequence as VS
import Control.Parallel.Strategies
import Control.Concurrent.Bag.Task (Interruptible (..))
import qualified Control.Concurrent.Bag.Implicit as Implicit
import System.IO.Unsafe (unsafePerformIO)
import Control.Concurrent.STM (TChan)

instance Monad C_SearchTree where
  return = C_Value

  C_Fail d  >>= _ = C_Fail d
  C_Value x >>= f = f x
  C_Or x y  >>= f = C_Or (x >>= f) (y >>= f)

  Choice_C_SearchTree cd i x y >>= f = Choice_C_SearchTree cd i (x >>= f) (y >>= f)
  Choices_C_SearchTree cd i xs >>= f = Choices_C_SearchTree cd i (map (>>= f) xs)
  Guard_C_SearchTree cd cs x   >>= f = Guard_C_SearchTree cd cs (x >>= f)
  Fail_C_SearchTree cd info >>= _ = Fail_C_SearchTree cd info   

instance Functor C_SearchTree where
  fmap = liftM

instance Applicative C_SearchTree where
  pure  = return
  (<*>) = ap

instance MonadPlus C_SearchTree where
  mzero = C_Fail (Curry_Prelude.C_Int -1#)
  mplus = C_Or

instance Alternative C_SearchTree where
  (<|>) = mplus
  empty = mzero

instance MonadSearch C_SearchTree where
  splus            = Choice_C_SearchTree
  ssum             = Choices_C_SearchTree
  szero (I# d) _   = C_Fail (Curry_Prelude.C_Int d)
  constrainMSearch = Guard_C_SearchTree

external_d_C_someSearchTree :: NormalForm a => a -> Cover -> ConstStore -> C_SearchTree a
external_d_C_someSearchTree = encapsulatedSearch

external_d_C_parDfsStrategy :: Curry_Prelude.Curry a => C_SearchTree a -> Cover -> ConstStore -> VS.C_ValueSequence a
external_d_C_parDfsStrategy tree cv cs = case tree of
  C_Fail  d -> VS.d_C_failVS d cv cs
  C_Value x -> VS.d_C_addVS x (VS.d_C_emptyVS cv cs) cv cs
  C_Or l r  -> runEval $ do
    rs <- rpar $ external_d_C_parDfsStrategy r cv cs
    ls <- rseq $ external_d_C_parDfsStrategy l cv cs
    return $ VS.d_OP_bar_plus_plus_bar ls rs cv cs
  Choice_C_SearchTree cv' i l r ->
    narrow  cv' i (external_d_C_parDfsStrategy l cv cs) (external_d_C_parDfsStrategy r cv cs)
  Choices_C_SearchTree cv' i ts ->
    narrows cs cv' i (\z -> external_d_C_parDfsStrategy z cv cs) ts
  Fail_C_SearchTree cv' fi -> failCons cv' fi
  Guard_C_SearchTree cv' cs' t -> guardCons cv' cs' (external_d_C_parDfsStrategy t cv $! addCs cs' cs)
  _ -> failCons cv defFailInfo -- TODO: is this necessary

listOfValueSequences :: Curry_Prelude.Curry a => Cover -> ConstStore -> [VS.C_ValueSequence a] -> VS.C_ValueSequence a
listOfValueSequences cv cs [] =     VS.d_C_emptyVS cv cs
listOfValueSequences cv cs (x:xs) = VS.d_OP_bar_plus_plus_bar x (listOfValueSequences cv cs xs) cv cs

external_d_C_parBfsBagStrategy :: Curry_Prelude.Curry a => C_SearchTree a -> Cover -> ConstStore -> VS.C_ValueSequence a
external_d_C_parBfsBagStrategy tree cv cs =
  listOfValueSequences cv cs $ unsafePerformIO $ Implicit.newInterruptibleBag Implicit.Queue (Just (Implicit.takeFirst :: Implicit.SplitFunction (VS.C_ValueSequence a))) [bfsTask cv cs tree]

bfsTask :: Curry_Prelude.Curry a => Cover -> ConstStore -> C_SearchTree a -> Interruptible (VS.C_ValueSequence a)
bfsTask cv cs t =
  case t of
    C_Fail  d -> OneResult $ VS.d_C_failVS d cv cs
    C_Value x -> OneResult $ VS.d_C_addVS  x (VS.d_C_emptyVS cv cs) cv cs
    C_Or    l r -> AddInterruptibles [bfsTask cv cs l, bfsTask cv cs r]
    -- All constructors below mean that there is a some kind of non-determinism,
    -- we do not want to encapsulate this. This is why we do not follow the tree
    -- further here. This will be done lazily once the value is requested
    -- with this strategy.
    Choice_C_SearchTree cv' i l r ->
      OneResult $ narrow cv' i (external_d_C_parBfsBagStrategy l cv cs) (external_d_C_parBfsBagStrategy r cv cs)
    Choices_C_SearchTree cv' i ts ->
      OneResult $ narrows cs cv' i (\z -> external_d_C_parBfsBagStrategy z cv cs) ts
    Fail_C_SearchTree cv' fi -> OneResult $ failCons cv' fi
    Guard_C_SearchTree cv' cs' t ->
      OneResult $ guardCons cv' cs' (external_d_C_parBfsBagStrategy t cv $! addCs cs' cs)
    _ ->
      OneResult $ failCons cv defFailInfo

external_d_C_parDfsBagStrategy :: Curry_Prelude.Curry a => C_SearchTree a -> Cover -> ConstStore -> VS.C_ValueSequence a
external_d_C_parDfsBagStrategy tree cv cs =
  listOfValueSequences cv cs $ unsafePerformIO $ Implicit.newTaskBag Implicit.Stack (Just (Implicit.takeFirst :: Implicit.SplitFunction (VS.C_ValueSequence a))) [dfsTask cv cs tree]

dfsTask :: Curry_Prelude.Curry a => Cover -> ConstStore -> C_SearchTree a -> Implicit.TaskIO (VS.C_ValueSequence a) (Maybe (VS.C_ValueSequence a))
dfsTask cv cs t =
  case t of
    C_Fail  d -> return $ Just $ VS.d_C_failVS d cv cs
    C_Value x -> return $ Just $ VS.d_C_addVS  x (VS.d_C_emptyVS cv cs) cv cs
    C_Or l r -> do
      Implicit.addTaskIO $ dfsTask cv cs r
      dfsTask cv cs l
    Choice_C_SearchTree cv' i l r ->
      return $ Just $ narrow cv' i (external_d_C_parDfsBagStrategy l cv cs) (external_d_C_parDfsBagStrategy r cv cs)
    Choices_C_SearchTree cv' i ts ->
      return $ Just $ narrows cs cv' i (\z -> external_d_C_parDfsBagStrategy z cv cs) ts
    Fail_C_SearchTree cv' fi ->
      return $ Just $ failCons cv' fi
    Guard_C_SearchTree cv' cs' t ->
      return $ Just $ guardCons cv' cs' (external_d_C_parDfsBagStrategy t cv $! addCs cs' cs)
    _ ->
      return $ Just $ failCons cv defFailInfo
