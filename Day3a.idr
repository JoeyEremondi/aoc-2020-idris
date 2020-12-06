module Day3a

import System.File
import Data.Strings
import Data.Either
import Data.List
import Data.List.Quantifiers
import Data.List.Elem
import Decidable.Equality
import Data.Void
import Data.Fin
import Data.Nat
import Data.Vect
import Data.Fin.Extra

------------
-- Sine Helper functions
-----------

-- Convert Either to have Strings for the error case
stringEither : Show a => Either a b -> Either String b
stringEither = bimap show id


-- Print the value of an Either, or its error string
ePrint : Show a => Either String a -> IO ()
ePrint ma = case ma of
  Left e => putStrLn ("ERROR: " ++ e)
  Right x => putStrLn (show x)


------------
-- Data types describing and functions the solution
-----------

--Each square has either a tree or is open
data Contents = Tree | Open


-- A row is a vector of contents with the given length
Row : Nat -> Type
Row n = Vect n Contents

-- Count the trees in the nth square of a given row
count : Row length -> Fin length -> Nat
count row x  with (index x row)
  count row x  | Tree = 1
  count row x  | Open = 0

-- A map of given height is a vector with that many elements,
-- each containing a row of the same length
Map : (length : Nat) -> (height : Nat) -> Type
Map len height = Vect height (Row len)

-- Given a location in one row, get the next location
-- in the following row
nextX : {length : Nat} -> {auto ok: GT length Z} -> Fin length -> Fin length
nextX {length} x with (divMod (3 + (finToNat x)) length)
  nextX x | (Fraction _ _ _ r _) = r


-- A proof that, if we walk going 3 down 1 starting at
-- the given position in the top row of the map,
-- we meet the given number of trees
data WalkCount : (theMap : Map length height) -> (start : Fin length) -> (count : Nat) -> Type where
  -- We have either 0 or 1 trees in the last row
  Done : WalkCount [] start 0
  -- Otherwise, we have some number of trees, plus however many trees come after
  Step :
    {auto ok: GT length Z}
    -> {m : Map length height}
    -> {x : Fin length}
    -> {row : Row length}
    -> WalkCount m (nextX x) subCount
    -> WalkCount (row ::  m) x (count {length = length} row x + subCount)

-- A solution:
-- Given a map and a start point,
-- it contains a count, and a proof that the count is correct
record Soln {0 length : Nat} {0 height : Nat} (theMap : Map length height)  (start : Fin length) where
  constructor MkSoln
  {theCount : Nat}
  0 correct : WalkCount theMap start theCount

-- Show that the count is decidable for any map and start point
decCount : {length : Nat} -> {auto ok: GT length Z} -> (theMap : Map length height) -> (start : Fin length) -> Soln theMap start
decCount [] start = MkSoln Done
decCount ( row :: rows) start with (decCount rows (nextX start))
  decCount (row :: rows) start | (MkSoln pf) = MkSoln (Step pf)



-- ------------------------
-- -- Input processing
-- ------------------------


-- Try converting a string into a row
stringToContents : (length : Nat) -> List Char -> Either String (Row length)
stringToContents 0 [] = pure Nil
stringToContents (S n) ('.' :: rest) = (Open ::) <$> stringToContents n rest
stringToContents (S n) ('#' :: rest) = (Tree ::) <$> stringToContents n rest
stringToContents _ _ = Left "bad parse"


-- Our main function: read the input into a map
-- then find and print its solution
main : IO ()
main = do
  mContents <- readFile "Day3.in"
  soln <- pure $ do
    theLines <- lines <$> (stringEither mContents)
    case theLines of
      [] => Left "No input"
      (row :: rows) => do
      let height = S (length rows)
      let len = length row
      case len of
        Z => Left "Empty row"
        S len => do
          let rowVec = fromList (row :: rows)
          theMap <- traverse (stringToContents $ S len) $ map fastUnpack rowVec
          pure $ theCount $ decCount theMap FZ
  ePrint soln
  -- pure $ do
  --   lines <- lines <$> mContents
  --   let height = length lines
  --   case height of
  --     [] => Left "No input"
  --     (row :: rows) => do
  --       let len = length row
  --       pure ?ret
    -- traverse (\line => maybeToEither "Bad int" (parseInteger line)) lines
