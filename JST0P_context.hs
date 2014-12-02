module JST0P_context
       (
         ContextAn,
         JST0P_context.empty,
         empty_empty,
         JST0P_context.var_get,
         var_set,
         var_set_list,
         var_set_path_list,
         var_names,
         sol_set,
         context_min_constrain,
         context_sub_constrain,
         aug_context,
         deg_context
       ) where

---------------------------------
-- a environment describes Gamma and P of the typing rules
-- both are modeled as List of names and types.
-- The JST0P environment has furthermore a solution for the type variables with it from the JST0 type inference
---------------------------------

import Data.Map as Map
import Data.Set as Set

import JST0_types
import JST0_type_aux
import JST0P_types
import JST0P_constrain
import JST0_context (Context,var_get)
import JST0P_solution

import Debugging

type ContextAn = (MembersAn,SolutionP)

empty :: SolutionP -> ContextAn
empty sol = (Map.empty,sol)

empty_empty :: ContextAn
empty_empty = (Map.empty,solutionP_empty)

empty_c :: ContextAn -> ContextAn
empty_c (_g,sol) = (Map.empty,sol)

var_lookup :: ContextAn -> String -> Maybe (TypeAn,FieldType)
var_lookup (g,_sol) s = Map.lookup s g

var_set :: ContextAn -> String -> (TypeAn,FieldType) -> ContextAn
var_set (g,sol) s t = (Map.insert s t g,sol)

sol_lookup :: ContextAn -> Int -> TypeP
sol_lookup (_g,sol) t = solutionP_get sol t

var_get :: ContextAn -> String -> (TypeAn,FieldType)
var_get (g,sol) s = case (var_lookup (g,sol) s) of
  Just (t,psi) -> (t,psi)

var_set_list :: ContextAn -> [String] -> [(TypeAn,FieldType)] -> ContextAn
var_set_list e [] [] = e
var_set_list e (s:ss) (t:ts) = var_set (var_set_list e ss ts) s t

var_set_path :: ContextAn -> Path -> (TypeAn,FieldType) -> ContextAn
var_set_path g [] _t = g
var_set_path g (o:ps) (t,_psit) = let
  to = var_lookup g o
  tonew = case to of
    Just (tor,_psitor) -> objectAn_set_path tor ps (t,Definite)
    Nothing -> objectAn_set_path (JST0P_None,I 0) ps (t,Definite)
  in var_set g o (tonew,Definite)

var_set_path_list :: ContextAn -> [Path] -> [(TypeAn,FieldType)] -> ContextAn
var_set_path_list c [] [] = c
var_set_path_list c (p:ps) (t:ts) = let
  c2 = var_set_path c p t
  in var_set_path_list c2 ps ts

var_contains :: ContextAn -> String -> Bool
var_contains (g,sol) s = Map.member s g

var_names :: ContextAn -> [String]
var_names (g,_sol) = Map.keys g

var_names_set :: ContextAn -> Set String
var_names_set (g,_sol) = Map.keysSet g

sol_set :: ContextAn -> SolutionP -> ContextAn
sol_set (c,_sol) sol = (c,sol)

context_min_constrain :: ContextAn -> ContextAn -> (Int,Int) -> ([ConstrainAn],ContextAn,Int,Int)
context_min_constrain g1 g2 (a,b) = vars_min_constrain g1 g2 (a,b) (get_union_set g1 g2)

vars_min_constrain :: ContextAn -> ContextAn -> (Int,Int) -> [String] -> ([ConstrainAn],ContextAn,Int,Int)
vars_min_constrain g1 _g2 (a,b) [] = ([],empty_c g1,a,b)
vars_min_constrain g1 g2 (a,b) (s:ss) = let
  (c_ss,g,a_ss,b_ss) = vars_min_constrain g1 g2 (a,b) ss
  (c_s,t,a_s,b_s) = var_min_constrain g1 g2 (a_ss,b_ss) s
  in (concat [c_ss,c_s],JST0P_context.var_set g s t,a_s,b_s)

var_min_constrain :: ContextAn -> ContextAn -> (Int,Int) -> String -> ([ConstrainAn],(TypeAn,FieldType),Int,Int)
var_min_constrain g1 g2 (a,b) s = let
  ((t1,n1),psi1) = case var_lookup g1 s of
    Just tp -> tp
    Nothing -> ((JST0P_None,I 0),Potential)
  ((t2,n2),psi2) = case var_lookup g2 s of
    Just tp -> tp
    Nothing -> ((JST0P_None,I 0),Potential)
  (t,c_t) | (t1 == JST0P_None) = (t2,[])
          | (t2 == JST0P_None) = (t1,[])
          | otherwise = let
    tt = sol_lookup g1 a
    in  (tt,makeMin_An (t1,n1) (t2,n2) (tt,N b))
  c = [Gt [n1,n2] [N b]]                     
  in (concat[c,c_t],((t,N b),min_field_type psi1 psi2),a+1,b+1)

context_sub_constrain :: ContextAn -> ContextAn -> [ConstrainAn]
context_sub_constrain (g1,_sol1) (g2,_sol2) = makeMore_Members g1 g2
    
     
get_union_set :: ContextAn -> ContextAn -> [String]
get_union_set g1 g2 = Set.elems (Set.union (var_names_set g1) (var_names_set g2))


aug_context :: Context -> Int -> SolutionP -> (ContextAn,Int)
aug_context m b sol = aug_context_those m b sol (Map.keys m)

aug_context_those :: Context -> Int -> SolutionP -> [String] -> (ContextAn,Int)
aug_context_those _m b sol [] = (JST0P_context.empty sol,b)
aug_context_those m b sol (s:ss) = let
  (t,psi) = JST0_context.var_get m s
  (tp,b2) = case t of
    (JST0_TV a _ann) -> (solutionP_get sol a,b)
    _ -> inflateP t b
  (rest,bp) = aug_context_those m b2 sol ss
  in (var_set rest s ((tp,I 0),psi),bp)

deg_context :: ContextAn -> Context
deg_context (con,_sol) = Map.map (\(t,tf) -> (deflateAn t,tf)) con
