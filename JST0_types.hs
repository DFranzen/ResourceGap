module JST0_types (
  Type(..),
  HL_Type(..),
  Members,

  add_HL_types,
  get_HL_type,

  get_TVs,
  get_TVs_list,
  get_TVs_index,
  get_TVs_index_list,

  tv_get_info,
  tv_get_index,

  is_Function,
  is_Simple,
  is_Object,
  is_TV,

  get_first_TVindex,
  get_all_TVindex,
  
  min_type,
  min_field_type,

  object_empty,
  object_singleton,
  object_from_list,
  object_set_type,
  object_set_field_type,
  object_set_path,
  object_get_type,
  object_get_path,
  object_get_FieldType,
  object_contain_at_most,
  object_is_empty,
  object_get_fieldnames,
  object_get_Definites,
  object_get_singleton,
  object_get_singleton_parts,

  JST0_types.const,
  ) where
--get FieldType (since shared with JST0P)
import JST0_type_aux

import Data.Map as Map
import Data.Set as Set
import Data.List as List

import Debugging

type Members = Map String (Type,FieldType)

showMembers :: Members -> String
showMembers t = Map.foldWithKey (\s ty prv -> prv ++ (showMember s ty)) "" t

showMember :: String -> (Type,FieldType) -> String
showMember s (t,tf) = (show s) ++ ":" ++ (show t) ++ (show tf) ++ ","

data Type = JST0_None
          | JST0_WC -- wild card for the constraints

          | JST0_Int
          | JST0_Bool
          | JST0_String String  -- singleton type storing the actual value
            
	  | JST0_Object Recu_Variable Members
          | JST0_Alpha Recu_Variable -- alpha-variable for Recursion

          | JST0_Function Type [Type] Type
            
          | JST0_TV Int String -- Type variable: Int is unique ID String is descriptor

          deriving Eq

instance Show Type where
  show JST0_None = "NONE"
  show JST0_WC = "_"

  show JST0_Int = "Int"
  show JST0_Bool = "Bool"
  show (JST0_String s) = "String(" ++ (show s) ++ ")"
  
  show (JST0_Object alpha members) = "µ" ++ (show alpha) ++ ".{" ++ (showMembers members) ++ "}"
  show (JST0_Alpha a) = (show a)

  show (JST0_Function t1 t2 t3) =  (show t1) ++ "⨯" ++ (show t2) ++ "->" ++ (show t3)

  show (JST0_TV vid des) = "[[" ++ (show des) ++ "]]_" ++ (show vid)


------------------------------------------
-- Higher level Type information
--   Only care about Objects, Functions or Int, not about details inside those types
------------------------------------------

data HL_Type = HL_Function
             | HL_Object
             | HL_simple Type
             | HL_None
          deriving Eq

instance Show HL_Type where
  show (HL_Function) = "->"
  show (HL_Object) = "{}"
  show (HL_simple t) = "S(" ++ (show t) ++ ")"
  show (HL_None) = "_"


tv_get_info :: Type -> String
tv_get_info (JST0_TV vid des) = "TV_" ++ (show vid) ++ ": " ++ (show des)
tv_get_info (JST0_Alpha _) =""

tv_get_index :: Type -> Int
tv_get_index t | trace 30 (" tv_get_index "++ show t) False = undefined
tv_get_index (JST0_TV vid _des) = vid

-- return all the type variable indices inside a type
get_TVs :: Type -> (Map Int String)
get_TVs JST0_Int = Map.empty
get_TVs JST0_Bool = Map.empty
get_TVs (JST0_String _) = Map.empty
get_TVs (JST0_Object _ xs) = Map.fold (\(t,_) xs2-> Map.union (get_TVs t) xs2) Map.empty xs
get_TVs (JST0_None) = Map.empty
get_TVs (JST0_Function t1 t2 t3) = Map.unions [get_TVs t1, get_TVs_list t2, get_TVs t3]
get_TVs (JST0_Alpha _) = Map.empty
get_TVs t = Map.fromList [(tv_get_index t,tv_get_info t)]

get_TVs_list :: [Type] -> (Map Int String)
get_TVs_list ts = Map.unions (Prelude.map get_TVs ts)

-- return a set with all the indices of used TVs
get_TVs_index :: Type -> (Set Int)
get_TVs_index JST0_Int = Set.empty
get_TVs_index JST0_Bool = Set.empty
get_TVs_index (JST0_String _) = Set.empty
get_TVs_index (JST0_Object _ xs) = Map.fold (\(t,_) xs2-> Set.union (get_TVs_index t) xs2) Set.empty xs
get_TVs_index (JST0_None) = Set.empty
get_TVs_index (JST0_Function t1 t2 t3) = Set.unions [get_TVs_index t1, get_TVs_index_list t2, get_TVs_index t3]
get_TVs_index (JST0_Alpha _) = Set.empty
get_TVs_index t = Set.fromList [tv_get_index t]

get_TVs_index_list :: [Type] -> (Set Int)
get_TVs_index_list ts = Set.unions (Prelude.map get_TVs_index ts)


-- returns true if the two types are equal
-- TODO: implement object isEqual modulo unrolling
-- TODO: don't just check whether completely equal but also generate constraints which make them equal -> more programs typeable
isEqual :: Type -> Type -> Bool
isEqual t1 t2 |trace 30 ("isEqual " ++ show t1 ++ ", " ++ show t2) False = undefined
isEqual JST0_Int JST0_Int = True
isEqual JST0_Bool JST0_Bool = True
isEqual (JST0_String s1) (JST0_String s2) = (s1 == s2)
isEqual (JST0_Function t1 t2 t3) (JST0_Function t1p t2p t3p) =
  (isEqual t1 t1p) && (isEqual_list t2 t2p) && (isEqual t3 t3p)
isEqual (JST0_Object alpha1 mem1) (JST0_Object alpha2 mem2)= let
  (JST0_Object _ m1) = swap_alpha (JST0_Object alpha1 mem1) alpha1 (get_gamma alpha1)
  (JST0_Object _ m2) = swap_alpha (JST0_Object alpha2 mem2) alpha2 (get_gamma alpha2)
                                                           --let _ = putStr "Object"
  in members_isEqual m1 m2
isEqual (JST0_None) (JST0_None) = True
isEqual (JST0_Alpha a) (JST0_Alpha b) = (a==b)
isEqual (JST0_TV id1 _des1) (JST0_TV id2 _des2) = (id1 == id2)

isEqual_list :: [Type] -> [Type] -> Bool
isEqual_list a b = Prelude.and (Prelude.zipWith isEqual a b)

-- return the lower bound of two types
-- min_type of a type variable is not defined
-- min_type of a function and a non-function
--          or an object  and a non-object is not defined
-- JST0_None is the maximal type for everything
-- JST0_Object _ [] is the maximal object Type
min_type :: Type -> Type -> Type
min_type JST0_None t = t
min_type t JST0_None = t
min_type JST0_Int JST0_Int = JST0_Int
min_type JST0_Bool JST0_Bool = JST0_Bool
min_type (JST0_String _) (JST0_String s2) = JST0_String s2
min_type (JST0_Object a1 l) (JST0_Object a2 lp) = let
  (JST0_Object _ l1) = swap_alpha (JST0_Object a1 l) a1 (get_gamma a2)
  (JST0_Object _ l2) = swap_alpha (JST0_Object a2 lp) a2 (get_gamma a2)
  lres = min_list_type l1 l2
  obj = JST0_Object (get_gamma a2) lres
  in swap_alpha obj (get_gamma a2) a2
min_type (JST0_Function t1 t2 t3) (JST0_Function t1p t2p t3p) = 
  (JST0_Function (min_type_func t1 t1p) (min_type_func_list t2 t2p) (min_type_func t3 t3p))
  
  --case
  --(isEqual t1 t1p) && (isEqual t2 t2p) && (isEqual t3 t3p) of
  --  True -> (JST0_Function t1 t2 t3)
min_type (JST0_Alpha a) (JST0_Alpha ap) | a==ap = (JST0_Alpha a)


min_type_func :: Type -> Type -> Type
min_type_func JST0_None t = t
min_type_func t JST0_None = t
min_type_func t1 t2 | (isEqual t1 t2) = t1

min_type_func_list :: [Type] -> [Type] -> [Type]
min_type_func_list t1 [] = t1
min_type_func_list [] t2 = t2
min_type_func_list t1 t2 = Prelude.zipWith min_type_func t1 t2

min_list_type :: Members -> Members -> Members
min_list_type l1 l2 = let s1 = Map.keysSet l1
                          s2 = Map.keysSet l2
                          s = Set.union s1 s2
                      in min_list_those l1 l2 (Set.toList s)

--return the Map with all minimum types of m1 m2 with the keys s1
min_list_those :: Members -> Members -> [String] -> Members
min_list_those _ _ [] = Map.empty
min_list_those m1 m2 (x:xs) = let rest = min_list_those m1 m2 xs
                              in Map.insert x (min_list_this m1 m2 x) rest

min_list_this :: Members -> Members -> String -> (Type,FieldType)
min_list_this m1 m2 s = let (t1,f1) = case (Map.lookup s m1) of
                              Just t -> t
                              Nothing -> (JST0_None,Potential)
                            (t2,f2) = case (Map.lookup s m2) of
                              Just t -> t
                              Nothing -> (JST0_None,Potential)
                        in (min_type t1 t2,min_field_type f1 f2)
                            
min_field_type :: FieldType -> FieldType -> FieldType
min_field_type Definite _ = Definite
min_field_type _ Definite = Definite
min_field_type Potential Potential = Potential

max_field_type :: FieldType -> FieldType -> FieldType
max_field_type Potential _ = Potential
max_field_type _ Potential = Potential
max_field_type Definite Definite = Definite

never :: Type
never | False = JST0_None

swap_alpha :: Type -> Recu_Variable -> Recu_Variable -> Type
swap_alpha (JST0_Object a m) a1 a2 = if (a1==a2)
                                     then (JST0_Object a m)
                                     else let
                                       m_swap = Map.map (swap_alpha_field a1 a2) m
                                       in if (a1==a)
                                          then JST0_Object a2 m_swap
                                          else JST0_Object a m_swap
swap_alpha (JST0_Alpha a) a1 a2 | (a1 == a) = (JST0_Alpha a2)
                                | otherwise = JST0_Alpha a
swap_alpha (JST0_Function t1 t2 t3) a1 a2 =
  JST0_Function (swap_alpha t1 a1 a2) (swap_alpha_list t2 a1 a2) (swap_alpha t3 a1 a2)
swap_alpha t _ _ = t

swap_alpha_field :: Recu_Variable -> Recu_Variable -> (Type,FieldType) -> (Type,FieldType)
swap_alpha_field a1 a2 (t,ft) = (swap_alpha t a1 a2,ft)

swap_alpha_list :: [Type] -> Recu_Variable -> Recu_Variable -> [Type]
swap_alpha_list l a b = Prelude.map (\ls -> swap_alpha ls a b) l

-- Substitute a recursive variable for a type
subs_alpha :: Type -> Recu_Variable -> Type -> Type
subs_alpha (JST0_Alpha a) r t | (a == r) = t
                              | otherwise = (JST0_Alpha a)
subs_alpha (JST0_Object a mem) r t | a == r = (JST0_Object a mem)
                                   | otherwise = JST0_Object a (members_subs_alpha mem r t)
subs_alpha (JST0_Function o tx tp) r t =
  (JST0_Function (subs_alpha o r t) (subs_alpha_list tx r t) (subs_alpha tp r t))
subs_alpha t _r _t = t

subs_alpha_list:: [Type] -> Recu_Variable -> Type -> [Type]
subs_alpha_list l alpha t = Prelude.map (\ls -> subs_alpha ls alpha t) l

members_subs_alpha :: Members -> Recu_Variable -> Type -> Members
members_subs_alpha mem a t = Map.map (\(tm,ft) -> (subs_alpha tm a t,ft)) mem

is_Object :: Type -> Bool
is_Object (JST0_Object _ _) = True
is_Object _ = False

is_Function :: Type -> Bool
is_Function (JST0_Function _ _ _) = True
is_Function _ = False

is_Int :: Type -> Bool
is_Int (JST0_Int) = True
is_Int _ = False

is_Simple :: Type -> Bool
is_Simple JST0_Int = True
is_Simple JST0_Bool = True
is_Simple (JST0_String _) = True
is_Simple _ = False

is_TV :: Type -> Bool
is_TV (JST0_TV _id _des) = True
is_TV _ = False

-- return the first highest level index in the list
get_first_TVindex :: [Type] -> Int
get_first_TVindex [] = undefined
get_first_TVindex (x:xs) = case x of
  (JST0_TV a _ann) -> a
  _ -> get_first_TVindex xs

-- return all highes level indices in the list
get_all_TVindex :: [Type] -> Set Int
get_all_TVindex [] = Set.empty
get_all_TVindex (x:xs) = case x of
  (JST0_TV a _ann) -> Set.insert a (get_all_TVindex xs)
  _ -> get_all_TVindex xs
 
add_HL_types :: HL_Type -> HL_Type -> HL_Type
add_HL_types a b | trace 30 ("add_HL_type " ++ show a ++ " " ++ show b) False = undefined
add_HL_types HL_None t = t
add_HL_types t HL_None = t
add_HL_types HL_Function HL_Function = HL_Function
add_HL_types (HL_simple (JST0_String _)) (HL_simple (JST0_String s2)) = HL_simple (JST0_String s2)
add_HL_types (HL_simple t1) (HL_simple t2) | t1 == t2 = HL_simple t2
add_HL_types HL_Object HL_Object = HL_Object
add_HL_types a b | error ("not consistent type: " ++ show a ++ " <-> " ++ show b) = undefined

get_HL_type :: Type -> HL_Type
get_HL_type (JST0_Object _ _) = HL_Object
get_HL_type (JST0_Function _ _ _) = HL_Function
get_HL_type (JST0_Int) = HL_simple JST0_Int
get_HL_type (JST0_Bool) = HL_simple JST0_Bool
get_HL_type (JST0_String s) = HL_simple (JST0_String s)
get_HL_type JST0_WC = HL_None
get_HL_type _ = HL_None


------------------------------------------
-- Functions on Members
------------------------------------------

members_empty :: Members
members_empty = Map.empty

members_is_empty :: Members -> Bool
members_is_empty m = ((Map.size m) == 0)

-- Create a singleton Memebers object with the given field with the given type
members_singleton :: String -> (Type,FieldType) -> Members
members_singleton s t = Map.fromList [(s,t)]

-- Return a singleton Members object wich contains only the information about field s in the members list m
members_get_singleton :: Members -> String -> Members
members_get_singleton m s =
  members_singleton s (members_get m s)

members_from_list :: [(String,Type)] -> Members
members_from_list [] = members_empty
members_from_list ((s,t):xs) = members_set (members_from_list xs) s (t,Definite)


-- Return the information about the type of a field without the Maybe wrapping (None,Potential) in the failure case
members_get :: Members -> String -> (Type,FieldType)
members_get m s = case (Map.lookup s m) of
  Just t -> t
  Nothing -> (JST0_None,Potential)

members_get_type :: Members -> String -> Type
members_get_type m s = let (t,_) = members_get m s
                       in t

members_get_field_type :: Members -> String -> FieldType
members_get_field_type m s = let (_,tf) = members_get m s
                             in tf

-- Return the type of the field at the given path
members_get_path :: Members -> Path -> (Type,FieldType)
members_get_path m [s] = members_get m s
members_get_path m (s:ss) = let
  (told,fold) = members_get m s
  (tlo,flo) = object_get_path told ss
  fnew | fold == Potential = Potential
       | flo == Potential = Potential
       | otherwise = Definite
  in (tlo,fnew)


-- Set a field in a memberlist
members_set :: Members -> String -> (Type,FieldType) -> Members
members_set m s (t,tf) = Map.insert s (t,tf) m

members_set_type :: Members -> String -> Type -> Members
members_set_type m s t = let
  (_t,fold) = members_get m s
  in members_set m s (t,fold)

members_set_FieldType :: Members -> String -> FieldType -> Members
members_set_FieldType m s ft = let
  (told,_f) = members_get m s
  in members_set m s (told,ft)

members_set_path :: Members -> Path -> (Type,FieldType) -> Members
members_set_path m [s] t = members_set m s t
members_set_path m (s:ss) t = let
  (told,f_old) = members_get m s
  (_t,tf) = t
  fnew | tf == Definite = Definite
       | otherwise = f_old
  tnew = object_set_path told ss t
  in members_set m s (tnew,fnew)


-- Return True iff the given field exists in the given members List
members_field_exists :: Members -> String -> Bool
members_field_exists m s = case (Map.lookup s m) of
  Just _ -> True
  Nothing -> False

members_contain_at_most :: Members -> [String] -> Bool
members_contain_at_most mems defs =
  Map.foldWithKey (\s (_,psi) b -> (b && ((psi == Potential) || (List.elem s defs)))) True mems

members_isEqual :: Members -> Members -> Bool
members_isEqual mem1 mem2 = let (_,res) = Map.foldWithKey (\s (t,f) (m,b) -> (m,(members_agree s (t,f) m) && b)) (mem2,True) mem1
                            in res

members_agree :: String -> (Type,FieldType) -> Members -> Bool
members_agree s (t,tf) mem = ((t,tf) == members_get mem s)

------------------------------------------
-- Functions on Objects
------------------------------------------

-- Create / compare to empty object
object_empty :: Recu_Variable -> Type
object_empty a = (JST0_Object a members_empty)

object_is_empty :: Type -> Bool
object_is_empty (JST0_Object _ mem) = members_is_empty mem

object_contain_at_most :: Type -> [String] -> Bool
object_contain_at_most t ss | trace 2 ("object_contain_at_most " ++ show t) False = undefined
object_contain_at_most (JST0_Object _ mem) ss = members_contain_at_most mem ss

-- Return an object with one field of the given name and type
object_singleton :: Recu_Variable -> String -> Type -> FieldType -> Type
object_singleton a s t f = JST0_Object a (members_singleton s (t,f))

object_from_list :: Recu_Variable -> [(String,Type)] -> Type
object_from_list a l = JST0_Object a (members_from_list l)

-- Return the different parts of information for one field in the given object type separate
object_get_singleton_parts :: Type -> String -> (Recu_Variable,Type,FieldType)
object_get_singleton_parts (JST0_Object a mem) s = let
  (t,tf) = members_get mem s
  in (a,t,tf)

-- Return a singleton object, which contains only the information about one field of the given object
object_get_singleton :: Type -> String -> Type
object_get_singleton (JST0_Object a mem) s = (JST0_Object a (members_get_singleton mem s))

-- return one field of the object:
object_get :: Type -> String -> (Type,FieldType)
object_get (JST0_Object a mem) m = let
  (t,tf) = members_get mem m
  in (subs_alpha t a (JST0_Object a mem),tf)

object_get_type :: Type -> String -> Type
object_get_type o m = let
  (t,_tf) = object_get o m
  in t

object_get_FieldType :: Type -> String -> FieldType
object_get_FieldType o m = let
  (_t,tf) = object_get o m
  in tf

object_get_path :: Type -> Path -> (Type,FieldType)
object_get_path (JST0_Object a mem) p = let
  (t,tf) = members_get_path mem p
  in (subs_alpha t a (JST0_Object a mem),tf)

-- Set a field of the object:
object_set :: Type -> String -> (Type,FieldType) -> Type
object_set (JST0_Object a mem) s t = JST0_Object a (members_set mem s t)

object_set_type :: Type -> String -> Type -> Type
object_set_type (JST0_Object a mem) s t = JST0_Object a (members_set_type mem s t)

object_set_field_type :: Type -> String -> FieldType -> Type
object_set_field_type (JST0_Object a mem) s t = JST0_Object a (members_set_FieldType mem s t)

object_set_path :: Type -> Path -> (Type,FieldType) -> Type
object_set_path  t1 p t2 | trace 30 ("object_set_path " ++ show p ++ "\n") False = JST0_None
object_set_path (JST0_Object a m) p t = JST0_Object a (members_set_path m p t)
object_set_path (JST0_None) p t = JST0_Object NotRec (members_set_path members_empty p t)


-- Returns true iff the given field exists in the given object
object_field_exists :: Type -> String -> Bool
object_field_exists (JST0_Object _ mem) s = members_field_exists mem s

-- Returns a list of fieldnames of the given object
object_get_fieldnames :: Type -> [String]
object_get_fieldnames (JST0_Object _ mem) = Map.keys mem
object_get_fieldnames _ = []

object_get_Definites :: Type -> [String]
object_get_Definites o = let
  fields = object_get_fieldnames o
  in List.filter (\s -> ((object_get_FieldType o s) == Definite)) fields

const :: Type -> Bool
const (JST0_TV _ _) = False
const _ = True
