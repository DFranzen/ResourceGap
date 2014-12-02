module JST0_context
       (
         Context ,
         JST0_context.empty ,
         var_get ,
         var_set ,
         var_set_list,
         context_min,
         context_min_constrain
       ) where

---------------------------------
-- a environment describes Gamma and P of the typing rules
-- both are modeled as List of names and types.
---------------------------------

import Data.Map as Map
import Data.Set as Set

import JST0_types
import JST0_type_aux
import JST0_constrain

type Context = Members
--             Variabletypes   

empty :: Context
empty = Map.empty

-- return saved type of variable s in the context gamma
-- if it does not exist, TV with id a is returned
-- Integer returned is the next TV index to be used
var_get :: Context -> String -> (Type,FieldType)
var_get gamma s = case (Map.lookup s gamma) of
   (Just t) -> t
   Nothing -> let t | error ("Variable " ++ s ++ " not defined") True = undefined
              in t

var_set :: Context -> String -> (Type,FieldType) -> Context
var_set gamma s t = Map.insert s t gamma

var_set_list :: Context -> [String] -> [(Type,FieldType)] -> Context
var_set_list e [] [] = e
var_set_list e (s:ss) (t:ts) = var_set (var_set_list e ss ts) s t
                            

-- generate a context that is smaller than g1 and g2
context_min :: Context -> Context -> Context
context_min g1 g2 = let
  (JST0_Object alpha g) = min_type (JST0_Object NotRec g1) (JST0_Object NotRec g2)
  in g
  --mergeWithKey var_min id id g1 g2

--var_min :: String -> (Type,FieldType) -> (Type,FieldType) -> Maybe (Type,FieldType)
--var_min _s t1 t2 = Just (min_type t1 t2)

-- Generate Constraints to make G1 a SubContext (extension of SubType) of G2
-- NOT NEEDED at the moment as Contexts update monotonically

--subContext :: Context -> Context -> [Constrain]
--subContext g1 g2 = context_subTypes (

--context_subTypes :: Context -> Context -> Int -> 
  
-- Generate the Constraints necessary to make the resulting Context a smaller context than g1 and g2
context_min_constrain :: Context -> Context -> Int -> ([Constrain],Context,Int)
context_min_constrain g1 g2 a = vars_min_constrain g1 g2 a (get_union_set g1 g2)

vars_min_constrain :: Context -> Context -> Int -> [String] -> ([Constrain],Context,Int)
vars_min_constrain _g1 _g2 a [] = ([],JST0_context.empty,a)
vars_min_constrain g1 g2 a (s:ss) = let
  (c_ss,g,a_ss) = vars_min_constrain g1 g2 a ss
  (c_s,t,a_s) = var_min_constrain g1 g2 a_ss s
  in (concat [c_ss,c_s],Map.insert s t g,a_s)

var_min_constrain :: Context -> Context -> Int -> String -> ([Constrain],(Type,FieldType),Int)
var_min_constrain g1 g2 a s = let
  (t1,tf1) = case Map.lookup s g1 of
    Just tp -> tp
    Nothing -> (JST0_None,Potential)
  (t2,tf2) = case Map.lookup s g2 of
    Just tp -> tp
    Nothing -> (JST0_None,Potential)
  (t,c) | (t1 == JST0_None) = (t2,[])
        | (t2 == JST0_None) = (t1,[])
        | otherwise = ((JST0_TV a (s ++ "_merge")), [SubType t1 t,SubType t2 t])
  in (c,(t,min_field_type tf1 tf2),a+1)


        
get_union_set :: Context -> Context -> [String]
get_union_set g1 g2 = Set.elems (Set.union (Map.keysSet g1) (Map.keysSet g2))
  
