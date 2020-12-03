module Day1b

import System.File
import Data.Strings
import Data.Either
import Data.List
import Data.List.Quantifiers
import Data.List.Elem
import Decidable.Equality

-- Convert Either to have Strings for the error case
stringEither : Show a => Either a b -> Either String b
stringEither = bimap show id

-- Convert Dec into Either
decEither : Dec a -> Either String a
decEither (Yes a) = Right a
decEither (No b) = Left "No solution"

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

-- Helper to convert from List Any proofs to Elem**prop proofs
anyElem : {0 p : a -> Type} -> {l : List a} -> Any p l -> (x : a ** (Elem x l, p x))
anyElem {l = x :: xs} (Here pf) = MkDPair x (Here, pf)
anyElem {l = x :: xs} (There pf) with (anyElem pf)
  anyElem {l = x :: xs} (There pf) | (el ** (elin , elpf)) = (el ** (There elin , elpf))

-- Helper to convert a proof that an element of a list has a property
-- into an Any proof for that list
elemAny : {0 p : a -> Type} -> {l : List a} -> {x : a} -> Elem x l -> p x -> Any p l
elemAny Here px = Here px
elemAny (There y) px = There (elemAny y px)

--What does a certificate of a solution look like?
--Given an input list of integers, it's a solution, with a pair of two integers,
--  proofs that they were both in the input, a proof that they
-- sum to 2020, and a proof that the solution is their product
record Soln (l : List Int) where
  constructor MkSoln
  {soln : Int}
  {entry1 : Int}
  {entry2 : Int}
  {entry3 : Int}
  in1 : Elem entry1 l
  in2 : Elem entry2 l
  in3 : Elem entry3 l
  sum2020 : entry1 + entry2 + entry3 = 2020
  solnProduct : entry1 * entry2 * entry3 = soln

-- Given an integer and a list, decide whether any of the integers
-- in the list sum to 2020 with the given int
find2020Partner : (l : List Int) ->(i : Int)  -> Dec (Any (\i2 => i + i2 = 2020) l)
find2020Partner l i = any (\i2 => decEq (i + i2) 2020) l

--Given a list, decide whether any integers in the list
-- sum to 2020
find2020Triple : (l : List Int) -> Dec (Any (\i1 => Any (\i2 => Any (\i3 => i1 + i2 + i3 = 2020) l) l) l)
find2020Triple l = any (\i1 => any (\i2 => find2020Partner l _) l) l

-- Given a proof that there is a pair satisfying the property, make a proper
-- solution record
makeSoln :
   (l : List Int)
   -> Any (\i1 => Any (\i2 => Any (\i3 => i1 + i2 + i3 = 2020) l) l) l
   -> Soln l
makeSoln l anyPf with (anyElem anyPf)
  makeSoln l anyPf  | (i1 ** (elem1 , anyPf2)) with (anyElem anyPf2)
    makeSoln l anyPf  | (i1 ** (elem1 , anyPf2)) | (i2 ** (elem2 , anyPf3)) with (anyElem anyPf3)
      makeSoln l anyPf  | (i1 ** (elem1 , anyPf2)) | (i2 ** (elem2 , anyPf3)) | (i3 ** (elem3 , sumPf)) =
      MkSoln elem1 elem2 elem3 sumPf Refl


-- Given a list of integers, determine whether there is a solution
-- to the problem, given that list
find2020Soln : (l : List Int) -> Dec (Soln l)
find2020Soln inputs = case find2020Triple inputs of
  Yes pf => Yes (makeSoln inputs pf)
  No npf => No (\ (MkSoln in1 in2 in3 eq _) => npf (elemAny in1 (elemAny in2 (elemAny in3 eq))))

-- Parse our input, find the solution, then print it
main : IO ()
main = do
  mInts <- readInput "Day1a.in"
  ePrint $ do
    ints <- mInts
    solnCert <- decEither $ find2020Soln ints
    pure (soln solnCert)
