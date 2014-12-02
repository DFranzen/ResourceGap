module JST0P_constrain where

import JST0P_types
import JST0_type_aux

import Data.Map as Map

import Debugging

-- Annotated constraints
-- TODO think where we actually need them
data ConstrainAn = Gt [Annotation] [Annotation]

instance Show ConstrainAn where
  show (Gt s1 s2) = (show_sum s1) ++ ">=" ++ (show_sum s2) ++ "\n"

-- show a sum represented as the list of summands
show_sum :: [Annotation] -> String
show_sum ([]) = "0"
show_sum [x] = (show x)
show_sum (x:xs) = (show x) ++ "+" ++ (show_sum xs)

----------------------------------------
-- compute constraints to make the resources in t1 less than t2
----------------------------------------
makeLess_Member :: (TypeAn,FieldType) -> (TypeAn,FieldType) -> [ConstrainAn]
makeLess_Member (t1,_f1) (t2,_f2) = makeLess_An t1 t2

makeLess_Members :: MembersAn -> MembersAn -> [ConstrainAn]
makeLess_Members mem1 mem2 = Map.foldrWithKey
                             (\k t c -> concat [makeLess_Member (membersAn_get mem1 k) t,c])
                             []
                             mem2

makeLess_An :: TypeAn -> TypeAn -> [ConstrainAn]
makeLess_An (t1,n1) (t2,n2) = concat [[Gt [n2] [n1]],makeLess_P t1 t2]

makeLess_P :: TypeP -> TypeP -> [ConstrainAn]
makeLess_P (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) = let
  (m1,m2) = equalize_alpha (JST0P_Object a1 mem1) (JST0P_Object a2 mem2)
  in makeLess_Members m1 m2
makeLess_P a b = makeEqual_P a b

makeLess_list :: [TypeP] -> [TypeP] -> [ConstrainAn]
makeLess_list as bs = concat (Prelude.zipWith makeLess_P as bs)

----------------------------------------
-- compute constraints to make the resources in t1 more than t2
----------------------------------------
makeMore_Member :: (TypeAn,FieldType) -> (TypeAn,FieldType) -> [ConstrainAn]
makeMore_Member (t1,_f1) (t2,_f2) = makeMore_An t1 t2
--FieldType Relation is already enforced from cg

makeMore_Members :: MembersAn -> MembersAn -> [ConstrainAn]
makeMore_Members mem1 mem2 = Map.foldrWithKey
                             (\k t c -> concat [makeMore_Member (membersAn_get mem1 k) t,c])
                             []
                             mem2

makeMore_An :: TypeAn -> TypeAn -> [ConstrainAn]
makeMore_An (t1,n1) (t2,n2) = concat [[Gt [n1] [n2]],makeMore_P t1 t2]

makeMore_P :: TypeP -> TypeP -> [ConstrainAn]
makeMore_P (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) = let
  (m1,m2) = equalize_alpha (JST0P_Object a1 mem1) (JST0P_Object a2 mem2)
  in makeMore_Members m1 m2
makeMore_P a b = makeEqual_P a b

makeMore_list :: [TypeP] -> [TypeP] -> [ConstrainAn]
makeMore_list as bs = concat (Prelude.zipWith makeMore_P as bs)

----------------------------------------
-- compute Constraints to make two types subtypes
----------------------------------------
makeSubtype_FieldType :: FieldType -> FieldType -> [ConstrainAn]
makeSubtype_FieldType a b | isSubtype_FieldType a b = []

makeSubtype_Member :: (TypeAn,FieldType) -> (TypeAn,FieldType) -> [ConstrainAn]
makeSubtype_Member (t1,f1) (t2,f2) = concat [makeSubtype_FieldType f1 f2,makeSubtype_An t1 t2]

makeSubtype_Members :: MembersAn -> MembersAn -> [ConstrainAn]
makeSubtype_Members mem1 mem2 = Map.foldrWithKey
                                (\k t c -> concat [c,
                                                   makeSubtype_Member (membersAn_get mem1 k) t])
                                []
                                mem2

makeSubtype_An :: TypeAn -> TypeAn -> [ConstrainAn]
makeSubtype_An (t1,a1) (t2,a2) = concat [makeSubtype_P t1 t2,[Gt [a1] [a2]]]

makeSubtype_P :: TypeP -> TypeP -> [ConstrainAn]
makeSubtype_P (JST0P_Function o t n tp np) (JST0P_Function o2 t2 n2 tp2 np2) = let
  co = makeEqual_P o o2
  ct = makeEqual_list t t2
  ctp= makeEqual_P tp tp2
  cn = [Gt [n2] [n]]
  cnp= [Gt [np,n2] [n,np2]]
  in concat [co,ct,ctp,cn,cnp]
makeSubtype_P (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) = let
  (m1,m2) = equalize_alpha (JST0P_Object a1 mem1) (JST0P_Object a2 mem2)
  in makeSubtype_Members m1 m2
makeSubtype_P a b | (a==b) = []
-- makeSubtype_P (JST0P_Alpha (Gamma a1)) (JST0P_Object (Beta a2) _)| (a1 == a2) = []
-- makeSubtype_P (JST0P_Object (Beta a2) _) (JST0P_Alpha (Gamma a1))| (a1 == a2) = []

makeSubtype_list :: [TypeP] -> [TypeP] -> [ConstrainAn]
makeSubtype_list [] [] = []
makeSubtype_list (x:xs) (y:ys) = let
  c = makeSubtype_P x y
  cs = makeSubtype_list xs ys
  in concat [c,cs]

----------------------------------------
-- compute Contraints to make the resources in t1 equal to those in t2
----------------------------------------
makeEqual_Member :: (TypeAn,FieldType) -> (TypeAn,FieldType) -> [ConstrainAn]
makeEqual_Member (t1,_f1) (t2,_f2) = makeEqual_An t1 t2
-- The fieldType has already been verified in the first step of the inference

makeEqual_Members :: MembersAn -> MembersAn -> [ConstrainAn]
makeEqual_Members mem1 mem2 = Map.foldrWithKey
                              (\k t c -> concat[makeEqual_Member (membersAn_get mem1 k) t,c])
                              []
                              mem2

makeEqual_An :: TypeAn -> TypeAn -> [ConstrainAn]
makeEqual_An (t1,a1) (t2,a2) = concat [[Gt [a1] [a2],Gt [a2] [a1]],makeEqual_P t1 t2]

makeEqual_P :: TypeP -> TypeP -> [ConstrainAn]
makeEqual_P t1 t2 | trace 2 ("makeEqual_P " ++ show t1 ++ " <-> " ++  show t2) False = undefined
makeEqual_P (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) = let
  (m1,m2) = equalize_alpha (JST0P_Object a1 mem1) (JST0P_Object a2 mem2)
  in makeEqual_Members m1 m2
makeEqual_P (JST0P_Function o1 t1 n1 tp1 np1) (JST0P_Function o2 t2 n2 tp2 np2) = let
  co = makeEqual_P o1 o2
  ct = makeEqual_list t1 t2
  ctp = makeEqual_P tp1 tp2
  cn = [Gt [n1] [n2],Gt [n2] [n1],
        Gt [np1] [np2],Gt [np2] [np1]]
  in concat[cn,co,ct,ctp]
makeEqual_P a b | (a==b) = []

makeEqual_list :: [TypeP] -> [TypeP] -> [ConstrainAn]
makeEqual_list as bs = concat (Prelude.zipWith makeEqual_P as bs)

----------------------------------------
-- Compute set of Constraints to make the three types match the Split definition
----------------------------------------

--makeSplit_FieldType :: FieldType -> FieldType -> FieldType -> [ConstrainAn]
--makeSplit_FieldType Definite Definite Definite = []
--makeSplit_FieldType _ _ Potential = []

makeSplit_Member :: (TypeAn,FieldType) -> (TypeAn,FieldType) -> (TypeAn,FieldType) -> [ConstrainAn]
makeSplit_Member (t1,f1) (t2,f2) (t3,f3) | f1 == f2 && f2==f3 = makeSplit_An t1 t2 t3

makeSplit_P :: TypeP -> TypeP -> TypeP -> [ConstrainAn]
--makeSplit_P t1 t2 t3 | trace 2 (
makeSplit_P (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) (JST0P_Object a3 mem3) = let
  (m1,m2,m3) = equalize_alpha3 (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) (JST0P_Object a3 mem3)
  in makeSplit_Members m1 m2 m3
makeSplit_P t1 t2 t3 | (t1==t2) && (t2==t3) = []

makeSplit_An :: TypeAn -> TypeAn -> TypeAn -> [ConstrainAn]
makeSplit_An (t1,n1) (t2,n2) (t3,n3) = concat [makeSplit_P t1 t2 t3,[Gt [n1,n2] [n3],Gt [n3] [n1,n2]]]

makeSplit_Members :: MembersAn -> MembersAn -> MembersAn -> [ConstrainAn]
makeSplit_Members mem1 mem2 mem3 | ((Map.keysSet mem1) == (Map.keysSet mem2)) && ((Map.keysSet mem2) == (Map.keysSet mem3)) =
  Map.foldrWithKey
  (\k t c -> concat[c,
                    makeSplit_Member (membersAn_get mem1 k) (membersAn_get mem2 k) t])
  []
  mem3

----------------------------------------
-- Compute set of Constraints to make the three types match the minimum Relation
----------------------------------------

makeMin_FieldType :: FieldType -> FieldType -> FieldType -> [ConstrainAn]
makeMin_FieldType Definite Definite Definite = []
makeMin_FieldType _ _ Potential = []

makeMin_Member :: (TypeAn,FieldType) -> (TypeAn,FieldType) -> (TypeAn,FieldType) -> [ConstrainAn]
makeMin_Member (t1,f1) (t2,f2) (t3,f3) = concat [makeMin_An t1 t2 t3,makeMin_FieldType f1 f2 f3]

makeMin_Members :: MembersAn -> MembersAn -> MembersAn -> [ConstrainAn]
makeMin_Members mem1 mem2 mem3 | ((Map.keysSet mem1) == (Map.keysSet mem2)) && ((Map.keysSet mem2) == (Map.keysSet mem3)) =
  Map.foldrWithKey
  (\k t c -> concat [c,
                     makeMin_Member (membersAn_get mem1 k) (membersAn_get mem2 k) t])
  []
  mem3

makeMin_An :: TypeAn -> TypeAn -> TypeAn -> [ConstrainAn]
makeMin_An (t1,n1) (t2,n2) (t3,n3) = concat [makeMin_P t1 t2 t3,[Gt [n2] [n3],Gt [n1] [n3]]]

makeMin_P :: TypeP -> TypeP -> TypeP -> [ConstrainAn]
makeMin_P (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) (JST0P_Object a3 mem3) = let
  (m1,m2,m3) = equalize_alpha3 (JST0P_Object a1 mem1) (JST0P_Object a2 mem2) (JST0P_Object a3 mem3)
  in makeMin_Members m1 m2 m3
makeMin_P t1 t2 t3 | (t1==t2) && (t2==t3) = []
                   | error ("Minimum of not compatible types required") = undefined
                   | otherwise = undefined


----------------------------------------
-- Compute a set of constraints that guarantees, that the given type does not hold any resource tickets
----------------------------------------

makeEmpty_P :: TypeP -> [ConstrainAn]
makeEmpty_P (JST0P_Object _alpha mem) = makeEmpty_Members mem
makeEmpty_P _ = []

makeEmpty_An :: TypeAn -> [ConstrainAn]
makeEmpty_An (t,n) = concat [[Gt [I 0] [n]],makeEmpty_P t]

makeEmpty_Members :: MembersAn -> [ConstrainAn]
makeEmpty_Members mem = Map.fold (\(t,_ft) r -> concat [r,makeEmpty_An t]) [] mem 
