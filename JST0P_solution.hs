module JST0P_solution where

import Data.Map as Map

import JST0P_types
import JST0_types
import JST0_type_aux
import JST0_solution

--import Debug.Trace

----------------------------------
-- represents a solution for type variables in JST0P
-- i.. a map from type variables to types
-- 
-- -note: a type in a solution has not type variables anymore
----------------------------------
type SolutionP = (Map Int TypeP)

-- return an empty solution
solutionP_empty :: SolutionP
solutionP_empty = Map.empty

-- replace all TV in the given type by their solution
solutionP_get :: SolutionP -> Int -> TypeP
solutionP_get s a = case Map.lookup a s of
  Just t1 -> t1
  Nothing -> (JST0P_None)

solutionP_set :: SolutionP -> Int -> TypeP -> SolutionP
solutionP_set s a t = Map.insert a t s

-- generate a solution in JST0P from a solution in JST0
solutionP_from_solution :: Solution -> (SolutionP,Int)
solutionP_from_solution s = solutionP_from_solutionlist s (Map.keys s)

-- Add annotations to a JST0 solution for all variables with indices in the given list. Returns the JST0P solution and the next usable index.
solutionP_from_solutionlist :: Solution -> [Int] -> (SolutionP,Int)
solutionP_from_solutionlist _ [] = (solutionP_empty,0)
solutionP_from_solutionlist s (x:xs) = let
  (solP,b) = solutionP_from_solutionlist s xs
  (t,b1) = (inflateP (solution_get s x) b)
  in ((solutionP_set solP x t),b1)

show_solutionP :: SolutionP -> String
show_solutionP s = Map.foldWithKey (\i t prv -> prv ++ show_solutionP_one i t) "" s

show_solutionP_one :: Int -> TypeP -> String
show_solutionP_one i t = (show i) ++ " -- " ++ (show t) ++ "\n"
