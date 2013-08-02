module CLPB (Boolean, true, false, neg, (.&&.), (.||.), satisfied) where

infixr 3 .&&.
infixr 2 .||.

data Boolean = B Int

true :: Boolean
true = B 1

false :: Boolean
false = B 0

neg :: Boolean -> Boolean
neg (B x) = B $ (prim_neg $!! x) result
 where result free

prim_neg :: Int -> Int -> Int
prim_neg external

(.&&.) :: Boolean -> Boolean -> Boolean
(B x) .&&. (B y) = B $ ((prim_and $!! x) $!! y) result
 where result free
       
prim_and :: Int -> Int -> Int -> Int
prim_and external

(.||.) :: Boolean -> Boolean -> Boolean
(B x) .||. (B y) = B $ ((prim_or $!! x) $!! y) result
 where result free

prim_or :: Int -> Int -> Int -> Int
prim_or external

satisfied :: Boolean -> Success
satisfied (B x) = (prim_sat $!! x) unknown

prim_sat :: Int -> Int -> Success
prim_sat external
