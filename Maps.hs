module Maps where

import Data.Map as Map
import Data.Set as Set

import JST0_types
import JST0_constrain

----------------------------------------
-- Higher Level Map
--  save the HL type of each TV
----------------------------------------

type HL_Map = Map Int HL_Type

hl_map_set :: HL_Map -> Type -> HL_Type -> HL_Map
hl_map_set m (JST0_TV a _ann) t = hl_map_seti m a t

hl_map_seti :: HL_Map -> Int -> HL_Type -> HL_Map
hl_map_seti m a t = let
  cur = Map.lookup a m
  new = case cur of
    Nothing -> t
    Just told -> (add_HL_types told t)
  in Map.insert a new m

hl_map_set_set :: HL_Map -> Set Int -> HL_Type -> HL_Map
hl_map_set_set m s t = Set.fold (\a ma -> hl_map_seti ma a t) m s

hl_map_get :: HL_Map -> Type -> HL_Type
hl_map_get m (JST0_TV a _ann) = hl_map_geti m a

hl_map_geti :: HL_Map -> Int -> HL_Type
hl_map_geti m a = case Map.lookup a m of
  Just t -> t
  Nothing -> HL_None

--return the HL_type either from the map, or from the type itself
hl_get :: HL_Map -> Type -> HL_Type
hl_get m (JST0_TV a _ann) = hl_map_geti m a
hl_get _m t = get_HL_type t

hl_map_consistent :: HL_Map -> Type -> HL_Type -> Bool
hl_map_consistent m t ht = let
  hlt = hl_get m t
  in hlt == ht

hl_map_consistenti :: HL_Map -> Int -> HL_Type -> Bool
hl_map_consistenti m a ht = let
  hlt = hl_map_geti m a
  in hlt==ht

hl_map_consistent_pair :: HL_Map -> Type -> Type -> Bool
hl_map_consistent_pair m t1 t2 = let
  ht1 = hl_get m t1
  ht2 = hl_get m t2
  in ht1 == ht2
     
hl_map_consistent_pairi :: HL_Map -> Int -> Int -> Bool
hl_map_consistent_pairi m a1 a2 = let
  hlt1 = hl_map_geti m a1
  hlt2 = hl_map_geti m a2
  in hlt1 == hlt2

----------------------------------------
-- Constraint Set
--   save all the constraints without duplicates
----------------------------------------

type CSet = Map String Constrain

-- return true if the constraints map is empty
cset_is_empty :: CSet -> Bool
cset_is_empty s = Map.null s

cset_empty :: CSet
cset_empty = Map.empty

cset_insert :: Constrain -> CSet -> CSet
cset_insert c cm = Map.insert (show c) c cm

-- insert multiple Constraints into an existing Constraints Map
cset_insert_multi :: CSet -> [Constrain] -> CSet
cset_insert_multi cm cs = Prelude.foldr (cset_insert) cm cs

-- Convert a Map of Constraints into an easier to handle list.
cset_to_list :: CSet -> [Constrain]
cset_to_list m = Map.elems m

-- Convert a List of Constraints into a Map, so we don't get duplicates
cset_from_list :: [Constrain] -> CSet
cset_from_list cs = (cset_insert_multi cset_empty cs)

-- Check if a ConMap contains the given constrain
cset_contains :: CSet -> Constrain -> Bool
cset_contains m c = case Map.lookup (show c) m of
  (Just _) -> True
  Nothing -> False

-- insert with check, if it is already in there
-- Return:
--  - True if new constraints were inserted
--  - False if they already existed
cset_union_bool :: CSet -> CSet -> (CSet, Bool)
cset_union_bool cm cmp = let cs= cset_to_list cm
                    in Prelude.foldr (cset_insert_bool) (cmp,False) cs

cset_insert_bool :: Constrain -> (CSet,Bool) -> (CSet,Bool)
cset_insert_bool c (cm,b) = let bn = b || not(cset_contains cm c)
                                cmn = cset_insert c cm
                            in (cmn,bn)

----------------------------------------
-- Constraint Map
--   save all the constraints affecting each type variable
----------------------------------------

type CMap = Map Int ([Constrain])

cmap_empty :: CMap
cmap_empty = Map.empty

-- Add a constrain to the sorted constrain set
--  -> add to the list if index is already there
--  -> add new key with a singleton list, if not there yet
cmap_add :: CMap -> Type -> Constrain -> CMap
cmap_add m (JST0_TV a1 _ann1) c = let
  cur = Map.lookup a1 m
  new = case cur of
    Nothing -> [c]
    (Just cs) -> c:cs
  in Map.insert a1 new m
cmap_add m _ _ = m

cmap_from_list :: [Constrain] -> CMap
cmap_from_list [] = Map.empty
cmap_from_list (c:s) = let r = cmap_from_list s
                       in case c of
                         (Empty t) -> cmap_add r t c
                         (SubType t1 t2) -> cmap_add (cmap_add r t1 c) t2 c
                         (IsObject t) -> cmap_add r t c
                         (MemberExtend t _ t2) -> cmap_add (cmap_add r t2 c) t c
                         (Extend t1 t2) -> cmap_add (cmap_add r t1 c) t2 c
                         (Only t1 _) -> cmap_add r t1 c
                         (Only_type t1 t2) -> cmap_add (cmap_add r t1 c) t2 c

cmap_geti :: CMap -> Int -> [Constrain]
cmap_geti cmap tv = case Map.lookup tv cmap of
  Nothing -> []
  Just t -> t

----------------------------------------
-- TypeVariable map
--   Save the related TVs for each TV
----------------------------------------

type TVMap = Map Int (Set Int)

tvmap_empty :: CMap
tvmap_empty = Map.empty

tvmap_add :: TVMap -> Type -> Type -> TVMap
tvmap_add m (JST0_TV a1 _ann1) (JST0_TV a2 _ann2) = let
  cur = Map.lookup a1 m
  new = case cur of
    Nothing -> Set.singleton a2
    (Just cs) -> Set.insert a2 cs
  in Map.insert a1 new m
tvmap_add m _ _ = m

tvmap_add_pair :: TVMap -> Type -> Type -> TVMap
tvmap_add_pair m t1 t2 = tvmap_add (tvmap_add m t1 t2) t2 t1

tvmap_from_list :: [Constrain] -> TVMap
tvmap_from_list [] = Map.empty
tvmap_from_list (c:cs) = let r = tvmap_from_list cs
                         in case c of
                           (Empty _t) -> r
                           (SubType t1 t2) -> tvmap_add_pair r t1 t2
                           (MemberExtend t1 _ t2) -> tvmap_add_pair r t1 t2
                           (Extend t1 t2) -> tvmap_add_pair r t1 t2
                           (IsObject _t) -> r
                           (Only _t _s) -> r
                           (Only_type t1 t2) -> tvmap_add_pair r t1 t2

tvmap_geti :: TVMap -> Int -> Set Int
tvmap_geti tvmap tv = case Map.lookup tv tvmap of
  Nothing -> Set.empty
  Just t -> t
