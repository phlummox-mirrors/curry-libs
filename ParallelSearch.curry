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
--- @version November 2013
------------------------------------------------------------------------------

module ParallelSearch
  ( getAllValues
  , getOneValue
  , parSearch
  , evalSearch
  , fairSearch
  , conSearch
  ) where

--- Gets all values of an expression using the given Strategy. 
getAllValues :: Strategy a -> a -> IO [a]
getAllValues external

--- Get any value of the expression using the given Strategy
getOneValue :: Strategy a -> a -> IO (Maybe a)
getOneValue external

data Strategy _ -- precise structure internally defined

--- Parallel strategy using Haskells par from Control.Parallel.
parSearch :: Strategy a
parSearch external

--- Parallel strategy using Haskells Eval monad.
evalSearch :: Strategy a
evalSearch external

--- Parallel strategy providing a fair search with concurrency.
fairSearch :: Strategy a
fairSearch external

--- Parallel search strategy implemented with concurrent Haskell.
--- The number given is the maximum number of threads.
conSearch :: Int -> Strategy a
conSearch external
