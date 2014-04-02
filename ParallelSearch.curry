------------------------------------------------------------------------------
--- This library contains implementations for parallel encapsulated search
--- similar to those in AllSolutions. In contrast to the search in
--- AllSolutions multiple values non-deterministic values will be
--- calculated in parallel.
--- 
--- This Module provides multiple parallel search strategies to select from.
--- If you are interested in a sequential strategy have a look at SearchTree.
--- 
--- @author  Bastian Holst
--- @version April 2014
------------------------------------------------------------------------------

module ParallelSearch
  ( getAllValues
  , getOneValue
  , getLazyValues
  , parSearch
  , fairSearch
  , conSearch
  , fairSearch'
  , fairSearch''
  , splitAll
  , splitAll'
  , splitLimitDepth
  , splitAlternating
  , splitPower
  , bfsParallel
  , bfsParallel'
  , dfsBag
  , dfsBagCon
  , dfsBagLimit
  , fdfsBag
  , fdfsBagCon
  , bfsBag
  , bfsBagCon
  , fairBag
  , fairBagCon
  , takeFirst
  , splitVertical
  , splitHalf
  , commonBuffer
  ) where

--- Gets all values of an expression using the given Strategy. 
getAllValues :: Strategy a -> a -> IO [a]
getAllValues external

--- Get any value of the expression using the given Strategy
getOneValue :: Strategy a -> a -> IO (Maybe a)
getOneValue external

getLazyValues :: Strategy a -> a -> IO [a]
getLazyValues external

data Strategy _ -- precise structure internally defined

--- Parallel strategy using Haskells par from Control.Parallel.
parSearch :: Strategy a
parSearch external
--- Parallel strategy providing a fair search with concurrency.
fairSearch :: Strategy a
fairSearch external

--- Parallel search strategy implemented with concurrent Haskell.
--- The number given is the maximum number of threads.
conSearch :: Int -> Strategy a
conSearch external

fairSearch' :: Strategy a
fairSearch' external

fairSearch'' :: Strategy a
fairSearch'' external

-- Strategies using Haskells Eval Monad

--- Parallel strategy using Haskells Eval monad.
splitAll :: Strategy a
splitAll external

splitAll' :: Strategy a
splitAll' external

splitLimitDepth :: Int -> Strategy a
splitLimitDepth external

splitAlternating :: Int -> Strategy a
splitAlternating external

splitPower :: Strategy a
splitPower external

--- Parallel breadth-first strategy.
--- Parallel strategy having the same lavel of completeness as the normal
--- breadth-first search, but evaluating all values of the current level in the
--- search tree in parallel. The values are given in the exact same order
--- compared to the sequencial breadth first search.
bfsParallel :: Strategy a
bfsParallel external

bfsParallel' :: Strategy a
bfsParallel' external

data SplitStrategy _ -- internally defined

dfsBag :: SplitStrategy a -> Strategy a
dfsBag external

dfsBagLimit :: SplitStrategy a -> Int -> Strategy a
dfsBagLimit external

dfsBagCon :: Strategy a
dfsBagCon external

fdfsBag :: SplitStrategy a -> Strategy a
fdfsBag external

fdfsBagCon :: Strategy a
fdfsBagCon external

bfsBag :: SplitStrategy a -> Strategy a
bfsBag external

bfsBagCon :: Strategy a
bfsBagCon external

fairBag :: SplitStrategy a -> Strategy a
fairBag external

fairBagCon :: Strategy a
fairBagCon external

commonBuffer :: SplitStrategy a
commonBuffer external

takeFirst :: SplitStrategy a
takeFirst external

splitVertical :: SplitStrategy a
splitVertical external

splitHalf :: SplitStrategy a
splitHalf external
