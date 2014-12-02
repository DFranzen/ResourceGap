module Closure (
  close_constraints,
  extract_solution,
  extract_HL_types
  ) where

-- import Data.Map
import Data.Map as Map
import Data.Set as Set

import Maps

import JST0_constrain
import JST0_types
import JST0_type_aux
import JST0_solution

import Debugging

-- API method to close a set of constraints
close_constraints :: [Constrain] -> [Constrain]
close_constraints _cs | trace 30 ("close_constraints \n\n") False = undefined
close_constraints c = let all1 = cset_from_list c
                      in cset_to_list (close_fix all1 all1)

-- close_fix S1 S2 S': Apply all the closure rules to pairs (c1,c2)\in S1xS2 as long as there is progress.
-- return all newly created constrains
close_fix :: CSet -> CSet -> CSet
close_fix s1 s2 = let _ = putStr "step starts"
                      new1 = closes s1 s2
                      _ = putStr "one step completed"
                      (all1,b) = cset_union_bool new1 s2
                  in if b
                     then Map.union (close_fix new1 all1) new1
                     else all1

-- close S1 S2 S': apply the closure rules to all pairs (s1,s2)\in S1xS2
-- returns all newly infered constraints
closes:: CSet -> CSet -> CSet
closes s1 s2 = if (cset_is_empty s1)
               then cset_empty
               else let (_,a) = Map.findMin s1
                        tail1 = Map.deleteMin s1
                    in Map.union (Map.union (close_with a s2) (close_single a)) (closes tail1 s2)

close_single :: Constrain -> CSet
close_single (SubType (JST0_Function t1 t2 t3) (JST0_Function t1p t2p t3p)) = let
  cset_res = cset_from_list (concat [[SubType t1 t1p,
                                     SubType t1p t1,
                                     SubType t3 t3p,
                                     SubType t3p t3],
                                    close_list t2 t2p,
                                    close_list t2p t2])
  in cset_res
close_single _ = cset_empty

close_list :: [Type] -> [Type] -> [Constrain]
close_list [] _ = []
close_list _ [] = []
close_list a b = close_listp a b

close_listp :: [Type] -> [Type] -> [Constrain]
close_listp [] [] = []
close_listp (x:xs) (y:ys) = (SubType x y):(close_list xs ys)

-- close_with c S S': apply the closure rule to all pairs (c,s)\in {c}xS
-- return all newly infered constrains S'
close_with:: Constrain -> CSet -> CSet
close_with c s = if (Map.size s == 0) 
                 then Map.empty
                 else let (_,elem1) = Map.findMin s
                      in Map.union (close_with c (Map.deleteMin s)) (close c elem1)

-- close c c' S': apply all closure rules to the pair c c' to obtain all indirect constraints in the set S'
close :: Constrain -> Constrain -> CSet
close (SubType t1 t1p) (Empty t) | t1 == t = let
  new = Empty t1p
  c = Map.insert (show new) new Map.empty
  in c
close (SubType t1 t1p) (SubType t2 t2p) = 
  let c = Map.empty
      -- closeTrans
      c1 = if ((t2==t1p) && (t2/=JST0_None))
           then let new = SubType t1 t2p
                in Map.insert (show new) new c
           else c
      -- closeTrans mirrored
      c2 = if ((t2p == t1) && (t1/=JST0_None))
           then let new = SubType t2 t1p
                in Map.insert (show new) new c1
           else c1
      -- closeBalance
      c3 = if ((t1==t2) &&(t1/=JST0_None))
           then case t2p of
             -- closeBalance
             (JST0_Function _ _ _) -> let new = (SubType t1p t2p)
                                      in Map.insert (show new) new c2
             (JST0_Int) -> let new = (SubType t1p t2p)
                           in Map.insert (show new) new c2
             (JST0_Bool) -> let new = (SubType t1p t2p)
                            in Map.insert (show new) new c2
             (JST0_String _) -> let new = (SubType t1p t2p)
                                in Map.insert (show new) new c2
             -- closeCong
             --(JST0_Object (Alpha _) (Map.fromList [(m,(t3,_))])) -> case t2 of
             (JST0_Object _ mem) -> case t1p of
               --(JST0_Object (Alpha _) [(mp,t3p,_)]) ->
               (JST0_Object _ mem2) -> let cons = members_closeCong t1p t2p (Map.keys (Map.intersection mem mem2))
                                       in cset_insert_multi c2 cons
               _ -> c2
             _ -> c2
           else c2
      -- closeBalance mirrored
      c4 = if ((t1==t2) && (t1/=JST0_None))
           then case t1p of
             -- closeBalance mirrored
             (JST0_Function _ _ _) -> let new = SubType t2p t1p
                                      in Map.insert (show new) new c3
             (JST0_Int) -> let new = SubType t2p t1p
                           in Map.insert (show new) new c3
             (JST0_Bool) -> let new = SubType t2p t1p
                            in Map.insert (show new) new c3
             (JST0_String _) -> let new = SubType t2p t1p
                                in Map.insert (show new) new c3
             _ -> c3
           else c3
  in c4
close (MemberExtend t1 mp t1p) (SubType t2 to) = 
  let -- closeTransMem
      c1 = if ((t1p==t2) && (t2/=JST0_None))
           then cset_from_list (members_closeTransMem t1 to (object_get_fieldnames to))
           else Map.empty
      -- closeBalanceMem
      c2 = if ((t1==t2) && (t2/=JST0_None))
           then cset_insert_multi c1 (members_closeBalanceMem t1p to mp (object_get_fieldnames to))
           else c1
  in c2
close (Extend t1 t1p) (SubType t2 to) | trace 30 ("close " ++ (show (Extend t1 t1p)) ++ ",  " ++ (show (SubType t2 to))) True =
  let --closeTransMem for Extend
    c1 = if ((t1p==t2) && (t2/=JST0_None))
         then cset_from_list (members_closeTransMem t1 to (object_get_fieldnames to))
         else Map.empty
    c2 = if ((t1==t2) && (t2/=JST0_None))
         then cset_insert_multi c1 (members_closeBalanceMems t1p to (object_get_fieldnames to))
         else c1
  in c2
-- closeTransMem, closeBalanceMem mirrored
-- do not mirror symmetric case
close (MemberExtend _ _ _) (MemberExtend _ _ _) = Map.empty
close (Extend _ _) (Extend _ _) = Map.empty
close t (MemberExtend t1 mp t2) = case t of
  (Extend _t1 _t2) -> Map.empty
  _ -> close (MemberExtend t1 mp t2) t
close t (Extend t1 t2) = close (Extend t1 t2) t
close _ _ = Map.empty

--members_closeBalanceMems: compute all the Constraints SubType t<[m:(tpp,Potential)] for m given in the list
members_closeBalanceMems :: Type -> Type -> [String] -> [Constrain]
members_closeBalanceMems _ _ [] = []
members_closeBalanceMems t to (m:ms) = let
  (a,tpp,_) = object_get_singleton_parts to m
  psip = Potential
  in (SubType t (object_singleton a m tpp psip)):(members_closeBalanceMems t to ms)

--members_closeTransMem: compute all the Constraints SubType t<[m:to(m)] for m given in the list
members_closeTransMem :: Type -> Type -> [String] -> [Constrain]
members_closeTransMem _ _ [] = []
members_closeTransMem t to (m:ms) = let
  (a,tpp,psi) = object_get_singleton_parts to m
  in (SubType t (object_singleton a m tpp psi)):(members_closeTransMem t to ms)

--members_closeBalanceMem: compute all the constraints t<[m:to(m)] where psi(mp)=Potential
members_closeBalanceMem :: Type -> Type -> String -> [String] -> [Constrain]
members_closeBalanceMem _ _ _ [] = []
members_closeBalanceMem t to mp (m:ms) = let
  (a,tpp,psi) = object_get_singleton_parts to m
  psip = if (m==mp)
         then Potential
         else psi
  in (SubType t (object_singleton a m tpp psip)):(members_closeBalanceMem t to mp ms)

--members_closeCong: compute all possible constraints tp<tpp in the closeCong case
-- Arguments:
--  - Object type from first subtyping relation
--  - Object type from second subtyping relation
--  - String which to use as m
-- Return
--  Set of constraints comning out of this case
members_closeCong :: Type -> Type -> [String] -> [Constrain]
members_closeCong _ _ [] = []
members_closeCong to1 to2 (m:ms) = let
  tp = object_get_type to1 m
  tpp = object_get_type to2 m
  rest = members_closeCong to1 to2 ms
  in (SubType tp tpp):((SubType tpp tp):rest)
     
-- close_count n S1 S2 S': close the constraints set S n times.
-- returns the newly created constraints in S'
close_count :: Int -> CSet -> CSet -> CSet
close_count 0 _ _ = cset_empty
close_count n s1 s2 = let new1 = closes s1 s2
                          all1 = Map.union new1 s2
                          new2 = close_count (n-1) new1 all1
                      in Map.union new1 new2

----------------------------------------
-- Close Dependencies between the TVs
----------------------------------------

-- Take a TVMap and a TV, return all TV from the set that are related to the TV
tvmap_close_one_with :: TVMap -> Int -> Set Int -> Set Int
tvmap_close_one_with tv_map tv s | (Set.null s) = tvmap_geti tv_map tv
tvmap_close_one_with tv_map tv s = let
  nxt = tvmap_geti tv_map tv
  nxt_c = tvmap_close_set tv_map (Set.intersection s nxt) (Set.difference s nxt)
  in Set.union nxt nxt_c

-- Take a TVMap and a set of TVs. Return all TV from the given set that are related to any TVs in the set
tvmap_close_set :: TVMap -> Set Int -> Set Int -> Set Int
tvmap_close_set tv_map s1 s2 = Set.fold (\tv r -> (Set.union (tvmap_close_one_with tv_map tv s2) r) ) Set.empty s1

tvmap_close_one :: TVMap -> Int -> TVMap
tvmap_close_one tv_map tv = let
  stv = Set.delete tv (Map.keysSet tv_map)
  nxt = tvmap_close_one_with tv_map tv stv
  in Map.insert tv nxt tv_map

tvmap_close_list :: TVMap -> [Int] -> TVMap
tvmap_close_list tv_map [] = tv_map
tvmap_close_list tv_map (tv:tvs) = let
  this_map = tvmap_close_one tv_map tv
  in tvmap_close_list this_map tvs

tvmap_close :: TVMap -> TVMap
tvmap_close tv_map = tvmap_close_list tv_map (Map.keys tv_map)

----------------------------------------
-- Extract HL types from the Constraint list
----------------------------------------

--extract the HL types of all TVs invoved
extract_HL_types :: [Constrain] -> (HL_Map)
extract_HL_types cs = let
  cs_map = cmap_from_list cs
  tv_map = tvmap_close (tvmap_from_list cs)
  tvs = Map.keysSet cs_map
  in extract_HL_type_set tvs tv_map cs_map

-- extract the HL types of all given TVs from the cmap and the tvmap
extract_HL_type_set :: (Set Int) -> TVMap -> CMap -> HL_Map
extract_HL_type_set s _tv_map _cs_map | Set.null s = Map.empty
extract_HL_type_set s  tv_map cs_map = let
  (tv,sn) = Set.deleteFindMax s      -- get next tv
  css = cmap_geti cs_map tv          -- get all cs for this tv
  hl_type = extract_HL_type_from css -- extract HL type from these cs
  in case hl_type of
    -- if we can't figure out that one, figure out the rest
    HL_None -> extract_HL_type_set sn tv_map cs_map
    -- if we figure out the HL type
    _ -> let
      nxt = tvmap_geti tv_map tv        -- find all neighbours
      snn = Set.difference sn nxt       -- remove them from TODO list
      rest = extract_HL_type_set snn tv_map cs_map  -- figure out rest
      hl_map_new = hl_map_seti rest tv hl_type
       in  hl_map_set_set hl_map_new nxt hl_type -- set all neighbours to the HL type

-- extract the HL type from all constraints about this TV
extract_HL_type_from :: [Constrain] -> HL_Type
extract_HL_type_from [] = HL_None
extract_HL_type_from (c:cs) = case c of
  (SubType t1 t2) -> extract_HL_type_pair t1 t2 cs
  (MemberExtend _t1 _m _t2) -> HL_Object
  (Extend t1 t2) -> extract_HL_type_pair t1 t2 cs
  (IsObject _t1) -> HL_Object
  (Only _t _m) -> HL_Object
  (Only_type t1 t2) -> extract_HL_type_pair t1 t2 cs
  (Empty _t ) -> HL_Object


-- two types are related, what does that mean for the HL type of each of them?
extract_HL_type_pair :: Type -> Type -> [Constrain] -> HL_Type
extract_HL_type_pair a b cs | trace 30 ("extract_HL_type_pair " ++ show a ++ "," ++ show b) False = undefined
extract_HL_type_pair (JST0_TV _a1 _ann1) (JST0_TV _a2 _ann2) cs = extract_HL_type_from cs
extract_HL_type_pair (JST0_TV _a2 _ann2) t cs  = add_HL_types (get_HL_type t) (extract_HL_type_from cs)
extract_HL_type_pair t (JST0_TV _a2 _ann2) cs = add_HL_types (get_HL_type t) (extract_HL_type_from cs)


----------------------------------------
-- Check that the Constraints are wellformed
----------------------------------------


-- check the wellformedness of the Constraints set and collect HL type information and sorted constraints on the way
-- Arguments: List of Constraints
-- Returns: Map from TV indices to Higher level type and set of Constraints for this TV
-- Will return matching error, if not well_formed
well_formed :: [Constrain] -> HL_Map -> Bool
well_formed [] _hlmap = True
well_formed (c:cs) hlmap = let
  rest = well_formed cs hlmap
  in rest && well_formed_one c hlmap

-- check one Constrain
-- Arguments: Constrain to handle and existing HL_Map
-- return: True if well formed
-- Will return matching error if not well_formed
well_formed_one :: Constrain -> HL_Map -> Bool
well_formed_one (Empty t) m = hl_map_consistent m t HL_Object
well_formed_one (Only t s) m = hl_map_consistent m t HL_Object
well_formed_one (Only_type t t2) m = hl_map_consistent m t HL_Object
well_formed_one (SubType t1 t2) m = hl_map_consistent_pair m t1 t2
well_formed_one (MemberExtend t1 s t2) m = hl_map_consistent_pair m t1 t2
well_formed_one (Extend t1 t2) m = hl_map_consistent_pair m t1 t2
well_formed_one (IsObject t) m = hl_map_consistent m t HL_Object

-------------------------------------------
-- Get the solution from the HL types
-------------------------------------------

--extracty the solution for all TVs from a bunch of closend constraints
-- Arguments:
--  - closed list of constraints
-- Returns: minimal Solution for all TVs
extract_solution :: [Constrain] -> Solution
extract_solution cs = let hl = extract_HL_types cs
                          cmap = cmap_from_list cs
                          sol = extract_solution_all (Map.keys cmap) (hl,cmap)
                          -- _correct | check_solution cs sol = True
                      in sol


--make a type TV-less
-- Arguments:
--  - Type to make TV-less
--  - Solution for all the TVs
-- Returns: alias type for the given type with all TV replaced by their solution (recursively)
extract_solution_type :: Type -> (HL_Map,CMap) -> Type
extract_solution_type t s = extract_type_type Set.empty s t

-- extract all solutions for the given TVs
-- Arguments:
--  - list of all indices for TVs to extract
--  - HigherLevel information about all the TVs
-- Returns solution for all TVs with indices in the first argument
extract_solution_all :: [Int] -> (HL_Map,CMap) -> Solution
extract_solution_all [] _ = solution_empty
extract_solution_all (i:is) (hl,cmap) = let typei = extract_type Set.empty (hl,cmap) i
                                            prv = extract_solution_all is (hl,cmap)
                                        in solution_set prv i typei

-- Main auxiliary function.
-- Arguments:
--  - Set of already bound recursive indices
--  - The HL type information
--  - index of the TV to infer a type for
-- Returns: Solution for all 
extract_type :: (Set Int) -> (HL_Map,CMap) -> Int -> Type
extract_type s (m,cmap) i = if (Set.member i s)
                            then JST0_Alpha (Beta i)
                            else let (t,cs) = (hl_map_geti m i,cmap_geti cmap i)
                                 in case t of
                                   HL_simple tp -> tp
                                   HL_None -> JST0_None
                                              --JST0_Object (Beta i) Map.empty --if we have no further constraints we assume it's an empty object (will work)
                                   HL_Function -> extract_type_function s (m,cmap) i cs
                                   HL_Object -> let
                                     sp = Set.insert i s --bind i
                                     inf = extract_type_object sp (m,cmap) i cs
                                     in inf

-- extract the type for a type from the HL_Map
-- what's the full solution for this type given these constraints
-- -> replace all type variables in this type by the appropriate solution
extract_type_type :: (Set Int) -> (HL_Map,CMap) -> Type -> Type
extract_type_type _ _ (JST0_Int) = JST0_Int
extract_type_type _ _ (JST0_Bool) = JST0_Bool
extract_type_type s m (JST0_Object a mem) = (JST0_Object a (extract_type_members s m mem))
extract_type_type _ _ (JST0_String st) = (JST0_String st)
extract_type_type s m (JST0_TV a _ann) = extract_type s m a
extract_type_type _ _ (JST0_Alpha a) = (JST0_Alpha a)
extract_type_type _ _ (JST0_None) = JST0_None
extract_type_type s m (JST0_Function t1 t2 t3) = (JST0_Function
                                                  (extract_type_type s m t1)
                                                  (extract_type_type_list s m t2)
                                                  (extract_type_type s m t3))

extract_type_type_list :: (Set Int) -> (HL_Map,CMap) -> [Type] -> [Type]
extract_type_type_list s m ts = Prelude.map (\t -> extract_type_type s m t) ts 

-- What's the full solution for this member type given these constraints
-- -> replace all typeVariables in this type by the approropriate solution
extract_type_member :: (Set Int) -> (HL_Map,CMap) -> (Type,FieldType) -> (Type,FieldType)
extract_type_member s m (t,ft) = (extract_type_type s m t,ft)
                                                 
-- extract the type of the member fields
-- i.e. get the appropriate type for all member types
extract_type_members :: (Set Int) -> (HL_Map,CMap) -> Members -> Members
extract_type_members s m mem = Map.map (extract_type_member s m) mem

-- extract the type of a function from the constraints
-- Arguments:
--  - Set of already bound Alpha indices
--  - Higher level types map
--  - Currently infered TV index
--  - All constraints concerning that TV
-- Returns: Type of this TV
extract_type_function :: (Set Int) -> (HL_Map,CMap) -> Int -> [Constrain] -> Type
extract_type_function s mp i cs = Prelude.foldr (\this rest -> extract_type_function_one s mp i this rest) (JST0_Function JST0_None [] JST0_None) cs
--extract_type_function s m i [] = JST0_Function JST0_None JST0_None JST0_None
--extract_type_function s m i [c] = extract_type_function_one s m i c
--extract_type_function s m i (c:cs) = let rest = extract_type_function s m i cs
--                                     in extract_type_function_one s m i c rest

--TODO: Do we need to think about typing rules t'<t to derive types for t?
-- specify the type of a function with one additional contraint
-- Arguments:
--  - Set of already bound Alpha indices
--  - Higher level types map
--  - Currently infered TV index
--  - All constraints concerning that TV
--  - current best guess for the type
-- Returns: newly refined type
extract_type_function_one :: (Set Int) -> (HL_Map,CMap) -> Int -> Constrain -> Type -> Type
extract_type_function_one s mp i (SubType (JST0_TV a _ann) t) tc
  | (a /= i)  = tc -- if this rule does not affect us -> no new constraints
  | otherwise =
    case t of
      (JST0_TV _a _ann) -> tc -- do not need to consider indirect subtypings, since already handled by closure
      _ -> min_type (extract_type_type s mp t) tc
extract_type_function_one _ _ _ (SubType _ _) tc = tc
                                                         

                                                                       
-- extract_type_function_one s m i _ = JST0_None -- constraints other than subtype should not occure for functions

extract_type_object :: (Set Int) -> (HL_Map,CMap) -> Int -> [Constrain] -> Type
extract_type_object s mp i cs = Prelude.foldr (\this rest -> extract_type_object_one s mp i this rest) (object_empty (Beta i)) cs
--extract_type_object _ _ _ [] = JST0_Object (Alpha 0) Map.empty
--extract_type_object s m i [c] = extract_type_object_one s m i c
--extract_type_object s m i (c:cs) = let rest = extract_type_object s m i cs
--                                   in (extract_type_object_one s m i c rest)

-- Returns upper bound for the type TV with the given index
extract_type_object_one :: (Set Int) -> (HL_Map,CMap) -> Int -> Constrain -> Type -> Type
extract_type_object_one s mp i c t |trace 30 ("extract_type_object_one: " ++ show c ) False = undefined
extract_type_object_one s mp i (SubType (JST0_TV a _ann) t) tc | (a /= i) = tc
                         -- if Constrain is speaking about other TV -> no new refinements
                                                         | otherwise  =
  case t of
    (JST0_TV _a _ann) -> tc -- indirect subtypings have been handled by closure
    _ -> min_type (extract_type_type s mp t) tc
extract_type_object_one _ _ _i (SubType _ _) tc = tc -- object_empty (Beta (i+100))
extract_type_object_one _ _ i (Empty (JST0_TV a _ann)) tc | (a==i) = tc --JST0_Object (Beta i) members_empty
extract_type_object_one _ _ i (Only (JST0_TV a _ann) _) tc
  | (a==i) = tc
  | otherwise = tc
extract_type_object_one _ _ i (Only_type (JST0_TV a _ann) _) tc
  | (a==i) = tc    -- Only_type is not handled here, but afterwards
  | otherwise = tc
extract_type_object_one s mp i (MemberExtend (JST0_TV a _ann) m t) tc | (a /= i) = tc
                                                               | otherwise =
  case t of
    (JST0_TV _a _ann) -> tc -- indirect constraints have been checked using closure
    (JST0_Alpha _) -> tc
    _ -> min_type (object_set_field_type (extract_type_type s mp t) m Definite) tc
extract_type_object_one s mp i (Extend (JST0_TV a _ann) t) tc | (a /= i) = tc
                                                       | otherwise =
  case t of
    (JST0_TV _a _ann) -> tc
    (JST0_Alpha _) -> tc
    _ -> min_type (extract_type_type s mp t) tc
extract_type_object_one _ _ _ (IsObject (JST0_TV _a _ann)) tc = tc


----------------------------------------
-- Check the solution fulfils the upper bounds
----------------------------------------

check_solution :: [Constrain] -> Solution -> Bool
check_solution [] sol = True
check_solution (c:cs) sol = let
  cm = lookup_constrain c sol
  in check_constrain_single cm

lookup_constrain :: Constrain -> Solution -> Constrain
lookup_constrain (SubType t1 t2) sol = SubType (lookup_type t1 sol) (lookup_type t2 sol)

lookup_type :: Type -> Solution -> Type
lookup_type (JST0_TV a _ann) sol = solution_get sol a
lookup_type t _sol= t

get_upper_bounds :: [Constrain] -> [Constrain]
get_upper_bounds [] = []
get_upper_bounds (c:cs) = let r = get_upper_bounds cs
                          in case c of
                            (Empty t) -> c:r
                            (Only _ _) -> c:r
                            (Only_type _ _) -> c:r
                            _ -> r
                            
