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
  , fairSearch
  , conSearch
  , splitAll
  , bfsParallel
  , dfsBag
  , fdfsBag
  , bfsBag
  , fairBag
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

--- Parallel strategy providing a fair search with concurrency.
fairSearch :: Strategy a
fairSearch external

--- Parallel search strategy implemented with concurrent Haskell.
--- The number given is the maximum number of threads.
conSearch :: Int -> Strategy a
conSearch external

-- Strategies using Haskells Eval Monad

--- Parallel strategy using Haskells Eval monad.
splitAll :: Strategy a
splitAll external

--- Parallel breadth-first strategy.
--- Parallel strategy having the same lavel of completeness as the normal
--- breadth-first search, but evaluating all values of the current level in the
--- search tree in parallel. The values are given in the exact same order
--- compared to the sequencial breadth first search.
bfsParallel :: Strategy a
bfsParallel external

dfsBag :: Strategy a
dfsBag external

fdfsBag :: Strategy a
fdfsBag external

bfsBag :: Strategy a
bfsBag external

fairBag :: Strategy a
fairBag external
