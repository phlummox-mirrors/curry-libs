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
  ) where

--- Gets all values of an expression using the given Strategy. 
getAllValues :: Strategy a -> a -> IO [a]
getAllValues external

--- Get any value of the expression using the given Strategy
getOneValue :: Strategy a -> a -> IO (Maybe a)
getOneValue str x = do
  vals <- getAllValues str x
  return (if null vals then Nothing else Just (head vals))

data Strategy _ -- precise structure internally defined

--- Parallel strategy using Haskells par from Control.Parallel.
parSearch :: Strategy a
parSearch external

--- Parallel strategy using Haskells Eval monad.
evalSearch :: Strategy a
evalSearch external
