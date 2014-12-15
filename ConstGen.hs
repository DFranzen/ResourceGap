module ConstGen where

import Language.JavaScript.Parser.AST
--import Language.JavaScript.Parser.SrcLocation
import JST0_types
import JST0_type_aux
import JST0_context
import JST0_constrain

import Debugging

import Conditionals
import Extraction

--import Data.List as List 

-- type
-- updated Environment
-- updated type variable count
-- constrains_types
type Con_out = (Int, Type, Context, [Constrain])
type Con_in = (Int, Context)

cg_JSNode :: Con_in -> JSNode -> Con_out
cg_JSNode (_a,_gamma) j | trace 30 ("\ncg_JSNode : " ++ (show j)) False = undefined
cg_JSNode (a,gamma) (NN (JSSourceElementsTop js)) = cg_JSNodes (a,gamma) js
cg_JSNode (a,gamma) (NN (JSLiteral "")) = (a, JST0_None,gamma,[])
cg_JSNode (a,gamma) (NN (JSExpression js)) = cg_JSNodes (a,gamma) js
cg_JSNode (a,gamma) (NN (JSVariables _var js _cont)) = cg_JSNodes (a,gamma) js
cg_JSNode (a,gamma) (NN (JSBlock _rb js _lb)) = cg_JSNodes (a,gamma) js
cg_JSNode (a,gamma) (NN (JSExpressionParen _rb j _lb)) = cg_JSNode (a,gamma) j
cg_JSNode (a,gamma) (NN n)
  | trace 30 "JSNode cases" False = undefined
  | is_Tnull_JS (NN n) = cg_Tnull (a,gamma)
  | is_TInt_JS (NN n) = cg_TInt (a,gamma)
  | is_TvarR_JS (NN n) = cg_TvarR (a,gamma) (ex_TvarR (NN n))
  | is_TmemR_JS (NN n) = cg_TmemR (a,gamma) (ex_TmemR (NN n))
  | is_Tcond_JS (NN n) = cg_Tcond (a,gamma) (ex_Tcond (NN n))
  | is_TvarD_JS (NN n) = cg_TvarD (a,gamma) (ex_TvarD (NN n))
  | is_TfunD_JS (NN n) = cg_TfunD (a,gamma) (ex_TfunD (NN n))
  | is_TobjD_JS (NN n) = cg_TobjD (a,gamma) (ex_TobjD (NN n))
  | is_TWhile_JS (NN n) = cg_TWhile (a,gamma) (ex_TWhile (NN n))
  | is_BoolResOp_JS (NN n) = cg_BoolResOp (a,gamma) (ex_BinOp_JS (NN n))
  | is_IntOp_JS (NN n) = cg_IntOp (a,gamma) (ex_BinOp_JS (NN n))
  | is_BoolOp_JS (NN n) = cg_BoolOp (a,gamma) (ex_BinOp_JS (NN n))
  | is_StringD_JS (NN n) = cg_StringD (a,gamma) (ex_StringD_JS (NN n))
--                           | otherwise = cg_Node (a,gamma) n
cg_JSNode (a,gamma) (NT n _l _c) | trace 30 "JSNode NT" True = cg_JSNode (a,gamma) (NN n)
cg_JSNode (a,gamma) j | trace 1 ("Not handled " ++ show j) True = (a,JST0_None,gamma,[])

cg_JSNode_list :: Con_in -> [JSNode] -> (Int,[Type],Context,[Constrain])
cg_JSNode_list (a,gamma) [] = (a,[],gamma,[])
cg_JSNode_list (a,gamma) (j:js) | is_irrellevant_JS j = (cg_JSNode_list (a,gamma) js)
                                | otherwise = let
  (a1,t1,g1,c1) = cg_JSNode (a,gamma) j
  (a2,ts,g2,c2) = cg_JSNode_list (a1,g1) js
  in (a2,t1:ts,g2,concat [c1,c2])

cg_Node :: Con_in -> Node -> Con_out
cg_Node (a,gamma) (JSSourceElementsTop js) = cg_JSNodes (a,gamma) js
cg_Node (a,gamma) (JSExpression js) = cg_JSNodes (a,gamma) js

--cg_Node (a,gamma) j
--  | is_funX j = let
--    (f,e) = ex_TfunX (NN j)
--    in cg_TfunX (a,gamma) f e
--  | is_int j = cg_TInt (a,gamma)
cg_Node (a,gamma) _ = (a,JST0_None,gamma,[])

cg_JSNodes :: Con_in -> [JSNode] -> Con_out
cg_JSNodes (a,gamma) js | trace 30 ("cg_JSNodes : " ++ show js) False = undefined
cg_JSNodes (a,gamma) js | is_TvarW_JS js = cg_TvarW (a,gamma) (ex_TvarW js)
                        | is_TmemW1_JS js = cg_TmemW1 (a,gamma) (ex_TmemW1 js)
                        | is_TmemW2_JS js = cg_TmemW2 (a,gamma) (ex_TmemW2 js)
                        | is_TmemX_JS js = cg_TmemX (a,gamma) (ex_TmemX js)
                        | is_TfunX_JS js = cg_TfunX (a,gamma) (ex_TfunX js)
                        | is_TnewX_JS js = cg_TfunX (a,gamma) (ex_TnewX js)
cg_JSNodes (a,gamma) [] = (a,JST0_None, gamma, [])
cg_JSNodes (a,gamma) [x] |trace 30 "JSNodes one" True = cg_JSNode (a,gamma) x
cg_JSNodes (a,gamma) (x:xs) | is_irrellevant_JS x = cg_JSNodes (a,gamma) xs
                            | otherwise = cg_TSeq (a,gamma) [x] xs



----------------------------------------
-- Rules for constraint generation
----------------------------------------

cg_Tnull :: Con_in -> Con_out
cg_Tnull (a,gamma) | trace 10 ("Tnull\n") False = undefined
cg_Tnull (a,gamma) = let
  -- create new TVs
  o = (JST0_TV a "Null Object")
  a0 = a + 1
  
  c = [IsObject o]
  in (a0,o,gamma,c)

cg_TInt :: Con_in -> Con_out
cg_TInt (a,gamma) | trace 10 ("cg_TInt") False = undefined
cg_TInt (a,gamma) = (a,JST0_Int,gamma,[])

cg_TvarR :: Con_in -> String -> Con_out
cg_TvarR (a,gamma) var | trace 10 ("cg_TvarR " ++ var) False = undefined
cg_TvarR (a,gamma) var = let
  -- create new variables
  t1 = (JST0_TV a (var ++ " copy to be stored back"))
  t2 = (JST0_TV (a+1) (var ++ " copy to be computed with"))
  a0 = a+2
  -- infer type
  (t_cand,psi_cand) = var_get gamma var
  t | psi_cand == Definite = t_cand
    | error ("Read from uninitialized variable: " ++ var) = undefined
    | otherwise = undefined
  gamma1 = var_set gamma var (t1,Definite)
  -- constraints
  c = [SubType t1 t,
       SubType t t1,
       SubType t2 t,
       SubType t t2]
  in (a0,t2,gamma1,c)

cg_TvarW :: Con_in -> (String,[JSNode]) -> Con_out
cg_TvarW (a,gamma) (x,e) | trace 10 ("TvarW") False = undefined
cg_TvarW (a,gamma) (x,e) = let
  -- create new variables
  txp = (JST0_TV a (x ++ " updated"))
  a0 = a + 1;
  -- infer types
  (tx,_psi) = var_get gamma x
  (a1,te,gamma1,c_1) = cg_JSNodes (a0,gamma) e
  gammap = var_set gamma1 x (txp,Definite)
  --constraints
  c = [SubType te tx,
       SubType txp te,
       Only_type txp te,
       Extend txp tx]
  in (a1,te,gammap,concat[c_1,c])

cg_TmemR :: Con_in -> ([JSNode],String) -> Con_out
cg_TmemR (a,gamma) (e,m) | trace 10 ("TmemR") False = undefined
cg_TmemR (a,gamma) (e,m) = let
  -- create new variables
  t2 = JST0_TV a ("MemberRead " ++ show m)
  a0 = a+1
  -- infer type
  (a1,o,gamma1,c_1) = cg_JSNodes (a0,gamma) e
  c = [SubType o (object_singleton NotRec m t2 Definite)]
  in (a1,t2,gamma1,concat [c_1,c])

cg_TmemW1 :: Con_in -> (String,String,JSNode) -> Con_out
cg_TmemW1 (a,gamma) (var,m,e) | trace 10 ("TmemW1 " ++ show a ) False = undefined
cg_TmemW1 (a,gamma) (var,m,e) = let
  -- create new variables
  tm = (JST0_TV a (var ++ "." ++ m))
  op = (JST0_TV (a+1) var)
  --tmp = (JST0_TV (a+2) (var ++ "." ++ m))
  a0 = a+3
  --infer type
  (o,_psi) = var_get gamma var
  (a1,te,gamma1,c_1) = cg_JSNode (a0,gamma) e
  gamma2 = var_set gamma1 var (op,Definite)
  -- constraints
  c = [SubType te tm,
       SubType o (object_singleton NotRec m tm Potential),
       SubType op (object_singleton NotRec m tm Definite),
       --SubType tmp te,
       --Only_type tmp te,
       --Extend tmp tm,
       MemberExtend op m o]
  in (a1,te,gamma2,concat [c_1,c])

cg_TmemW2 :: Con_in -> ([JSNode],String,JSNode) -> Con_out
cg_TmemW2 (a,gamma) (e1,m,e2) | trace 10 ("TmemW2") False = undefined
cg_TmemW2 (a,gamma) (e1,m,e2) = let
  -- create new variables
  tm = (JST0_TV a ("Member " ++ show m))
  a0 = a + 1
  -- infer typen
  (a1,o ,gamma1,c_1) = cg_JSNodes (a0,gamma) e1
  (a2,t2,gamma2,c_2) = cg_JSNode (a1,gamma1) e2
  c = [SubType o (object_singleton NotRec m tm Definite),
       SubType t2 tm]
  in (a2,t2,gamma2,concat [c_1,c_2,c])

cg_TmemX :: Con_in -> ([JSNode],String,[JSNode]) -> Con_out
cg_TmemX (a,gamma) ( e,m,ei) | trace 10 ("TmemX") False = undefined
cg_TmemX (a,gamma) (e,m,ei) = let
  -- aquire new variables
  f = (ex_code_list e) -- get identifier for the function
  g = (JST0_TV a f)
  o = (JST0_TV (a+1) (f ++ "_This"))
  tp = (JST0_TV (a+2) (f ++ "_Ret"))
  a0 = a+3
  (a1,tx) = cg_ArgList_copy a0 ei

  
  -- infer function type
  (a2,te,gamma1,c_e) = cg_JSNodes (a1,gamma) e
  c_te = [SubType te (object_singleton NotRec m g Definite)]
  c_f  = [SubType g (JST0_Function o tx tp)]
  
  -- infer argument types
  (a3,ti,gamma2,c_ei) = cg_JSNode_list (a2,gamma1) ei

  c = [SubType te o]
  c_arg = makeSubtype_list ti tx

  in (a3,tp,gamma2,concat[c,c_te,c_e,c_f,c_ei,c_arg])

cg_TfunX :: Con_in -> (String,[JSNode]) -> Con_out
cg_TfunX (a,gamma) (f,ei) |trace 30 ("TfunX: " ++ show f ++ "(" ++ show ei ++ "), \n" ++ show gamma) False = undefined
cg_TfunX (a,gamma) (f,ei) |trace 10 ("TfunX") False = undefined
cg_TfunX (a,gamma) (f,ei) = let
  -- acquire new Variables
  o = (JST0_TV a (f++"_This"))
  tp = (JST0_TV (a+1) (f++"_Ret"))
  a0 = a+2
  (a2,tx) = cg_ArgList_copy a0 ei

  -- infer function type
  (g_cand,psi) = var_get gamma f
  g | psi == Definite = g_cand
    | trace 1 ("Read from potential Function " ++ f) True = undefined
    | otherwise = undefined
  gamma1 = var_set gamma f (g,Definite)
  -- infer argument types
  (a4,ti,gamma2,c_ei) = cg_JSNode_list (a2,gamma1) ei
  c_f  = [SubType g (JST0_Function o tx tp)]

  c = [Empty o]
  c_arg = makeSubtype_list ti tx
  in (a4,tp,gamma2,concat[c,c_ei,c_arg,c_f])

cg_TSeq :: Con_in -> [JSNode] -> [JSNode] -> Con_out
cg_TSeq (a,gamma) e1 e2 | trace 10 ("TSeq") False = undefined
cg_TSeq (a,gamma) e1 e2 | is_irrellevant_list e1 = cg_JSNodes (a,gamma) e2
                        | is_irrellevant_list e2 = cg_JSNodes (a,gamma) e1
                        | otherwise = let
                          (a1,_t1,gamma1,c_1) = cg_JSNodes (a ,gamma ) e1
                          (a2, t2,gamma2,c_2) = cg_JSNodes (a1,gamma1) e2
                          in (a2,t2,gamma2,concat [c_1,c_2])


cg_Tcond :: Con_in -> (JSNode,[JSNode],[JSNode]) -> Con_out
cg_Tcond (a,gamma) (e1,e2,e3) | trace 10 ("Tcond") False = undefined
cg_Tcond (a,gamma) (e1,e2,e3) = let
  -- create new variables
  t = (JST0_TV a "Merge of if branches")
  a0 = a+1
  -- infer type
  (a1,tb,gamma1,c_1) = cg_JSNode (a0,gamma) e1
  (a2,tt,gamma2,c_2) = cg_JSNodes (a1,gamma1) e2
  (a3,tf,gamma3,c_3) = cg_JSNodes (a2,gamma1) e3
  (c_G,gammar,a4) = context_min_constrain gamma2 gamma3 a3
  c = [SubType tb JST0_Bool,
       SubType tf t,
       SubType tt t
      ]
  in (a4,t,gammar,concat [c,c_1,c_2,c_3,c_G])

cg_TvarD :: Con_in -> (String,JSNode) -> Con_out
cg_TvarD (a,gamma) (var,e) | trace 10 ("TvarD") False = undefined
cg_TvarD (a,gamma) (_var,e) = cg_JSNode (a,gamma) e

cg_TfunD :: Con_in -> (String,[String],JSNode) -> Con_out
cg_TfunD (a,gamma) (f,xi,e) | trace 10 ("Tfund") False = undefined
cg_TfunD (a,gamma) (f,xi,e) = let
    -- define variables
    tThis = JST0_TV a (f ++ "_This")
    a0 = a+1
    (a1,tx) = cg_ArgList a0 xi
    -- prepare contexts
    (tf,_psi) | f == ""   = (JST0_Function tThis tx te,Definite)
              | otherwise = var_get gamma f
    gammap | f == "" = gamma
           | otherwise = var_set gamma f (tf,Definite)
    gammafp = var_set_list gammap ("this":xi) (list2Def (tThis:tx))
    -- infer function body
    (a2,gammaf) = fp_JSNode (a1,gammafp) e
    (a3,te,_g1,c_1) = cg_JSNode (a2,gammaf) e
    -- put together result
    c | f == ""   = []
      | otherwise = [SubType tf (JST0_Function tThis tx te)]
    c_this = [IsObject tThis]
    in (a3,tf,gammap,concat[c_1,c,c_this])

cg_TobjD :: Con_in -> [(String,[JSNode])] -> Con_out
cg_TobjD (_a,_gamma1) _fields | trace 10 ("TObjD") False = undefined
cg_TobjD (a,gamma1) fields = let
  -- create TVs
  o = JST0_TV a "objLit"
  a0 = a+1
  -- infer type
  (ap,types,gammakp1,c1) = cg_fields (a0,gamma1) fields
  to = object_from_list NotRec types
  c = [SubType o to,
       Only_type o to]
  in (ap,o,gammakp1,concat [c,c1])

cg_TWhile :: Con_in -> (JSNode,JSNode) -> Con_out
cg_TWhile (_a,_gamma) (_bool,_e) | trace 10 ("TWhile") False = undefined
cg_TWhile (a,gamma) (bool,e) = let
  (a1,tb,gamma1,c_1) = cg_JSNode (a,gamma) bool
  (a2,_te,_gamma2,c_2) = cg_JSNode (a1,gamma1) e
  c = [SubType tb JST0_Bool]
  in (a2,JST0_None,gamma1,concat [c,c_1,c_2])

cg_BoolResOp :: Con_in -> ([JSNode],[JSNode]) -> Con_out
cg_BoolResOp (_a,_gamma) (_js1,_js2) | trace 10 ("BoolResOp") False = undefined
cg_BoolResOp (a,gamma) (js1,js2) = let
  (a1,t1,gamma1,c_1) = cg_JSNodes (a,gamma) js1
  (a2,t2,gamma2,c_2) = cg_JSNodes (a1,gamma1) js2
  c = [SubType t1 t2,SubType t2 t1]
  in (a2,JST0_Bool,gamma2,concat[c_1,c_2,c])

cg_IntOp :: Con_in -> ([JSNode],[JSNode]) -> Con_out
cg_IntOp (_a,_gamma) (_js1,_js2) | trace 10 ("IntOp") False = undefined
cg_IntOp (a,gamma) (js1,js2) = let
  (a1,t1,gamma1,c_1) = cg_JSNodes (a,gamma) js1
  (a2,t2,gamma2,c_2) = cg_JSNodes (a1,gamma1) js2
  c = [ SubType t1 JST0_Int,
        SubType t2 JST0_Int]
  in (a2,JST0_Int,gamma2,concat[c_1,c_2,c])

cg_BoolOp :: Con_in -> ([JSNode],[JSNode]) -> Con_out
cg_BoolOp (_a,_gamma) (_js1,_js2) | trace 10 ("IntOp") False = undefined
cg_BoolOp (a,gamma) (js1,js2) = let
  (a1,t1,gamma1,c_1) = cg_JSNodes (a,gamma) js1
  (a2,t2,gamma2,c_2) = cg_JSNodes (a1,gamma1) js2
  c = [ SubType t1 JST0_Bool,
        SubType t2 JST0_Bool]
  in (a2,JST0_Bool,gamma2,concat[c_1,c_2,c])

cg_StringD :: Con_in -> String -> Con_out
cg_StringD (_a,_gamma) s | trace 10 ("StringD: " ++ s) False = undefined
cg_StringD (a,gamma) _s =
  (a,JST0_String "",gamma,[])

----------------------------------------
-- Auxiliary Functions
----------------------------------------
list2Def :: [Type] -> [(Type,FieldType)]
list2Def = Prelude.map (\t -> (t,Definite))

cg_fields :: Con_in -> [(String,[JSNode])] -> (Int,[(String,Type)],Context,[Constrain])
cg_fields (a,gamma) [] = (a,[],gamma,[])
cg_fields (a,gamma) ((s,js):jx) = let
  (as,ts,gammas,c_s) = cg_JSNodes (a,gamma) js
  (ax,l ,gammax,c_x) = cg_fields (as,gammas) jx
  in (ax,(s,ts):l,gammax,concat[c_s,c_x])

cg_ArgList :: Int -> [String] -> (Int,[Type])
cg_ArgList a [] = (a,[])
cg_ArgList a (x:xs) = let
  tx = JST0_TV a x
  (as,txs) = cg_ArgList (a+1) xs
  in (as,tx:txs)

cg_ArgList_copy :: Int -> [a] -> (Int,[Type])
cg_ArgList_copy a [] = (a,[])
cg_ArgList_copy a (_x:xs) = let
  tx = JST0_TV a "Argument"
  (as,txs) = cg_ArgList_copy (a+1) xs
  in (as,tx:txs)


----------------------------------------
-- First pass
----------------------------------------

type FP_in = (Int,Context)
type FP_out = (Int,Context)

fp_JSNode :: FP_in -> JSNode -> FP_out
fp_JSNode (_a,_gamma) j | trace 30 ("\nfp_JSNode : " ++ (show j)) False = undefined
fp_JSNode (a,gamma) (NN (JSSourceElementsTop js)) = fp_JSNodes (a,gamma) js
fp_JSNode (a,gamma) (NN (JSLiteral "")) = (a,gamma)
fp_JSNode (a,gamma) (NN (JSExpression js)) = fp_JSNodes (a,gamma) js
fp_JSNode (a,gamma) (NN (JSVariables _var js _cont)) = fp_JSNodes (a,gamma) js
fp_JSNode (a,gamma) (NN (JSBlock _rb js _lb)) = fp_JSNodes (a,gamma) js
fp_JSNode (a,gamma) (NN (JSExpressionParen _rb j _lb)) = fp_JSNode (a,gamma) j
fp_JSNode (a,gamma) (NN n)
  | is_Tnull_JS (NN n) = (a,gamma)
  | is_TInt_JS (NN n) = (a,gamma)
  | is_TvarR_JS (NN n) = (a,gamma)
  | is_TmemR_JS (NN n) = fp_TmemR (a,gamma) (ex_TmemR (NN n))
  | is_Tcond_JS (NN n) = fp_Tcond (a,gamma) (ex_Tcond (NN n))
  | is_TfunD_JS (NN n) = fp_TfunD (a,gamma) (ex_TfunD (NN n))
  | is_TobjD_JS (NN n) = fp_TobjD (a,gamma) (ex_TobjD (NN n))
  | is_TvarD_JS (NN n) = fp_TvarD (a,gamma) (ex_TvarD (NN n))
  | is_TWhile_JS (NN n) = fp_TWhile (a,gamma) (ex_TWhile (NN n))
  | is_BoolResOp_JS (NN n) = fp_BinOp (a,gamma) (ex_BinOp_JS (NN n))
  | is_IntOp_JS (NN n) = fp_BinOp (a,gamma) (ex_BinOp_JS (NN n))
  | is_StringD_JS (NN n) = fp_StringD (a,gamma) (ex_StringD_JS (NN n))
fp_JSNode (a,gamma) (NT n _l _c) = fp_JSNode (a,gamma) (NN n)
fp_JSNode (a,gamma) j | trace 1 ("FP: Expression not handled" ++ show j) True = (a,gamma)
                      | True = undefined

fp_JSNodes :: FP_in -> [JSNode] -> FP_out
fp_JSNodes (a,gamma) js
  | is_TvarW_JS js = fp_TvarW (a,gamma) (ex_TvarW js)
  | is_TmemW1_JS js = fp_TmemW1 (a,gamma) (ex_TmemW1 js)
  | is_TmemW2_JS js = fp_TmemW2 (a,gamma) (ex_TmemW2 js)
  | is_TmemX_JS js = fp_TmemX (a,gamma) (ex_TmemX js)
  | is_TfunX_JS js = fp_TfunX (a,gamma) (ex_TfunX js)
  | is_TnewX_JS js = fp_TfunX (a,gamma) (ex_TnewX js)
fp_JSNodes (a,gamma) [] = (a,gamma)
fp_JSNodes (a,gamma) [x] = fp_JSNode (a,gamma) x
fp_JSNodes (a,gamma) (x:xs) = fp_TSeq (a,gamma) [x] xs

fp_TvarW :: FP_in -> (String,[JSNode]) -> FP_out
fp_TvarW (a,gamma) (_x,e) = fp_JSNodes (a,gamma) e

fp_TmemR :: FP_in -> ([JSNode],String) -> FP_out
fp_TmemR (a,gamma) (e,_m) = fp_JSNodes (a,gamma) e

fp_TmemW1 :: FP_in -> (String,String,JSNode) -> FP_out
fp_TmemW1 (a,gamma) (_var,_m,e) = fp_JSNode (a,gamma) e

fp_TmemW2 :: FP_in -> ([JSNode],String,JSNode) -> FP_out
fp_TmemW2 (a,gamma) (e1,_m,e2) =
  fp_JSNode (fp_JSNodes (a,gamma) e1) e2


fp_TmemX :: FP_in -> ([JSNode],String,[JSNode]) -> FP_out
fp_TmemX (a,gamma) (e1,_m,ei) = let
  (a1,gamma1) = fp_JSNodes (a,gamma) e1
  in fp_JSNodes (a1,gamma1) ei

fp_TfunX :: FP_in -> (String,[JSNode]) -> FP_out
fp_TfunX (a,gamma) (_f,ei) = fp_JSNodes (a,gamma) ei

fp_TSeq :: FP_in -> [JSNode] -> [JSNode] -> FP_out
fp_TSeq (a,gamma) e1 e2 | is_irrellevant_list e1 = fp_JSNodes (a,gamma) e2
                        | is_irrellevant_list e2 = fp_JSNodes (a,gamma) e1
                        | otherwise = fp_JSNodes (fp_JSNodes (a,gamma) e1) e2

fp_Tcond :: FP_in -> (JSNode,[JSNode],[JSNode]) -> FP_out
fp_Tcond (a,gamma) (e1,e2,e3) =
  fp_JSNodes (fp_JSNodes (fp_JSNode (a,gamma) e1) e2) e3

fp_TvarD :: FP_in -> (String,JSNode) -> FP_out
fp_TvarD (a,gamma) (var,e) = let
  tvar = JST0_TV a (var ++ "Decl")
  gammap = var_set gamma var (tvar,Potential)
  in fp_JSNode (a+1,gammap) e

fp_TfunD :: FP_in -> (String,[String],JSNode) -> FP_out
fp_TfunD (a,gamma) (f,_x,_e) | f=="" = (a,gamma)
                             | otherwise = let
  tf = JST0_TV a (f++"Decl")
  gammap = var_set gamma f (tf,Definite)
  in (a+1,gammap)

fp_TobjD :: FP_in -> [(String,[JSNode])] -> FP_out
fp_TobjD (a,gamma) [] = (a,gamma)
fp_TobjD (a,gamma) ((_s,js):jx) =
  fp_TobjD (fp_JSNodes (a,gamma) js) jx

fp_TWhile :: FP_in -> (JSNode,JSNode) -> FP_out
fp_TWhile (a,gamma) (bool,e) = fp_JSNode (fp_JSNode (a,gamma) bool) e

fp_BinOp :: FP_in -> ([JSNode],[JSNode]) -> FP_out
fp_BinOp (a,gamma) (js1,js2) = fp_JSNodes (fp_JSNodes (a,gamma) js1) js2

fp_StringD :: FP_in -> String -> FP_out
fp_StringD (a,gamma) _s = (a,gamma)
