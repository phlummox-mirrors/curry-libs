import Control.Monad
import Control.Applicative
import MonadSearch
import GHC.Exts (Int (I#))
import Strategies
import qualified Curry_ValueSequence as VS
import Control.Parallel.Strategies

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
