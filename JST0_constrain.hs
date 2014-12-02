module JST0_constrain where

import JST0_types
--import JST0_type_aux

import Data.Map as Map
--import Data.List as List

import Debugging

data Constrain = SubType Type Type
               | MemberExtend Type String Type
               | Extend Type Type
               | IsObject Type
               | Only Type [String] -- Type has not more than the following definite members
               | Only_type Type Type -- Type has not more definite members than the other                 
               | Empty Type
                 
instance Show Constrain where
  show (SubType t1 t2) = (show t1) ++ "≤" ++ (show t2)
  show (IsObject t) = "(" ++ (show t) ++ ")^{obj}"
  show (MemberExtend t1 m t2) = (show t1) ++ "⊲_" ++ (show m) ++ (show t2)
  show (Extend t1 t2) = (show t1) ++ "⊲_*" ++ (show t2)
  show (Empty t1) = (show t1) ++ "°"
  show (Only t1 s) = (show t1) ++ "≤_⚫" ++ (show s)
  show (Only_type t1 t2) = (show t1) ++ "≤_⚫" ++ (show t2)

----------------------------------------
-- check a set of constraints with no TVs
----------------------------------------

check_constrain_all :: [Constrain] -> Bool
check_constrain_all cs = Prelude.all check_constrain_single cs

check_constrain_single :: Constrain -> Bool
check_constrain_single c | trace 30 ("check_constrain_single " ++ show c) False = undefined
check_constrain_single (Empty t) | check_constrain_empty t = True
                                 | error "!! Emtpy type is required to have Definire MEmber" True = undefined
check_constrain_single (Only t defs) | object_contain_at_most t defs  = True
                                     | error "\n!!! Absent Member needs to be Definite" True = undefined
check_constrain_single (Only_type t t2) | trace 30 ("Check: " ++ show (Only_type t t2)) False = undefined
                                        | t == t2 = True
                                        | object_contain_at_most t (object_get_Definites t2) = True
                                        | error "\n!!! Potential Member needs to be Definite" True = undefined
check_constrain_single _ = True



----------------------------------------
-- check all the constraints for a particular solution for a type variable
----------------------------------------

check_constraints :: [Constrain] -> Type -> Bool
check_constraints cs t = Prelude.foldr (\a b -> (check_constrain a t) && b) True cs

check_constrain :: Constrain -> Type -> Bool
check_constrain (Empty _) t = check_constrain_single (Empty t)
check_constrain (Only _ defs) t = check_constrain_single (Only t defs)
check_constrain (Only_type _ t2) t = check_constrain_single (Only_type t t2)
check_constrain _ _ = True

----------------------------------------
-- single checking methods for constraints
----------------------------------------

check_constrain_empty :: Type -> Bool
check_constrain_empty t | object_contain_at_most t [] = True
                        | otherwise = False

--check_constrain_only :: Members -> [String] -> Bool
--check_constrain_only mems defs =
--  Map.foldWithKey (\s (_,psi) b -> (b && ((psi == Potential) || (List.elem s defs)))) True mems
--check_constrain_only _ _ = True


should_be_empty :: [Constrain] -> Bool
should_be_empty [] = False
should_be_empty ((Empty _):_) = True
should_be_empty (_:cs) = should_be_empty cs

cs_show_varinfo :: [Constrain] -> String
cs_show_varinfo cs = let tvs = get_type_variables cs
                     in Map.fold (\x prv -> (prv ++ "\n" ++ tv_show_info x)) "" tvs

-- return the indices of the used type variables
get_type_variables :: [Constrain] -> (Map Int Type)
get_type_variables [] = Map.empty
get_type_variables (a:xs) = let
  here= case a of 
    SubType t1 t2 -> Map.union (get_tv_inside t1) (get_tv_inside t2)
    --Equal t1 t2 -> Map.union (get_tv_inside t1) (get_tv_inside t2)
    IsObject t -> get_tv_inside t
    MemberExtend t1 _ t2 -> Map.union (get_tv_inside t1) (get_tv_inside t2)
    Extend t1 t2 -> Map.union (get_tv_inside t1) (get_tv_inside t2)
    Empty t -> get_tv_inside t
    Only t _ -> get_tv_inside t
    Only_type t _ -> get_tv_inside t
  in Map.union here (get_type_variables xs)

-- return all the type variable indices inside a type
get_tv_inside :: Type -> (Map Int Type)
get_tv_inside JST0_Int = Map.empty
get_tv_inside JST0_Bool = Map.empty
get_tv_inside (JST0_String _) = Map.empty
get_tv_inside (JST0_Object _ xs) = Map.fold (\(t,_) xs2-> Map.union (get_tv_inside t) xs2) Map.empty xs
get_tv_inside (JST0_None) = Map.empty
get_tv_inside (JST0_Function t1 t2 t3) = Map.unions [get_tv_inside t1, get_tv_inside_list t2, get_tv_inside t3]
get_tv_inside (JST0_Alpha _) = Map.empty
get_tv_inside t = Map.insert (tv_get_index t) t Map.empty

get_tv_inside_list :: [Type] -> (Map Int Type)
get_tv_inside_list [] = Map.empty
get_tv_inside_list (x:xs) = Map.unions [get_tv_inside x,get_tv_inside_list xs]

-- return all Constraints neccessary to make two lists component-wise subtypes
makeSubtype_list :: [Type] -> [Type] -> [Constrain]
makeSubtype_list = Prelude.zipWith (\a b -> (SubType a b)) 

