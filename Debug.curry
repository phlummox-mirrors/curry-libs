------------------------------------------------------------------------------
--- Library for debugging operations.
---
--- @author Björn Peemöller
--- @version September 2014
------------------------------------------------------------------------------

module Debug
  ( trace, traceId, traceShow, traceShowId, traceIO
  , assert, assertIO
  ) where

import IO     (hPutStrLn, stderr)
import Unsafe (unsafePerformIO)

--- Prints the first argument as a side effect and behaves as identity on the
--- second argument.
trace :: String -> a -> a
trace s x = unsafePerformIO (traceIO s >> return x)

--- Prints the first argument as a side effect and returns it afterwards.
traceId :: String -> String
traceId a = trace a a

--- Prints the first argument using `show` and returns the second argument
--- afterwards.
traceShow :: a -> b -> b
traceShow a b = trace (show a) b

--- Prints the first argument using `show` and returns it afterwards.
traceShowId :: a -> a
traceShowId a = trace (show a) a

--- Output a trace message from the `IO` monad.
traceIO :: String -> IO ()
traceIO m = hPutStrLn stderr m

--- Assert a condition w.r.t. an error message.
--- If the condition is not met it fails with the given error message,
--- otherwise the third argument is returned.
assert :: Bool -> String -> a -> a
assert cond s x = if cond then x else error s

--- Assert a condition w.r.t. an error message from the `IO` monad.
--- If the condition is not met it fails with the given error message.
assertIO :: Bool -> String -> IO ()
assertIO cond s = unless cond $ error s