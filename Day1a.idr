module Day1a

import System.File
import Data.Strings
import Data.Either
import Data.List

-- Convert Either to have Strings for the error case
stringEither : Show a => Either a b -> Either String b
stringEither = bimap show id

-- Print the value of an Either, or its error string
ePrint : Show a => Either String a -> IO ()
ePrint ma = case ma of
  Left e => putStrLn ("ERROR: " ++ e)
  Right x => putStrLn (show x)

-- Helper function to read a file into a bunch of integers
readInput : HasIO io => String -> io (Either String (List Int))
readInput filename = do
  mContents <- stringEither <$> readFile filename
  pure $ do
    lines <- lines <$> mContents
    traverse (\line => maybeToEither "Bad int" (parseInteger line)) lines


-- Given a list of integers, find the pair that sums to 2020
-- and return their product
find2020Pair : List Int -> Either String Int
find2020Pair inputs = do
  let potentials = (flip map) inputs $ \i1 => do
      i2 <- find (\i2 => i1 + i2 == 2020) inputs
      pure (i1 * i2)
  maybeToEither "No solution found" $ head' (catMaybes potentials)

-- Parse our input, find the solution, then print it
main : IO ()
main = do
  mInts <- readInput "Day1a.in"
  ePrint $ do
    ints <- mInts
    find2020Pair ints
