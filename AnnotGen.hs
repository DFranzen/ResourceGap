module AnnotGen (
  ag_JSNode,
  fpp_JSNode
  ) where

import Language.JavaScript.Parser.AST
--import Language.JavaScript.Parser.SrcLocation
import JST0P_types
import JST0_type_aux
import JST0P_context
import JST0P_constrain
import JST0P_solution

import Debugging

import Conditionals
import Extraction

import Res_model

--import Data.List as List 

-- type
-- updated Environment
-- updated type variable count
-- constrains_types
type Con_out = (Int, Int, TypeP, Annotation, ContextAn, [ConstrainAn])
type Con_in = (Int, Int, ContextAn, Annotation, SolutionP)

ag_JSNode :: Con_in -> JSNode -> Con_out
ag_JSNode gamma j | trace 30 ("ag_JSNode " ++ show j) False = undefined
ag_JSNode gamma (NN (JSSourceElementsTop js)) = ag_JSNodes gamma js
ag_JSNode (a,b,g,n,_sol) (NN (JSLiteral "")) = (a,b,JST0P_None,n,g,[])
ag_JSNode gamma (NN (JSExpression js)) = ag_JSNodes gamma js
ag_JSNode gamma (NN (JSVariables _var js _cont)) = ag_JSNodes gamma js
ag_JSNode gamma (NN (JSBlock _rb js _lb)) = ag_JSNodes gamma js
ag_JSNode gamma (NN (JSExpressionParen _rb j _lb)) = ag_JSNode gamma j
ag_JSNode gamma (NN n)
  | is_Tnull_JS (NN n) = ag_Tnull gamma
  | is_TInt_JS (NN n) = ag_TInt gamma
  | is_TvarR_JS (NN n) = ag_TvarR gamma (ex_TvarR (NN n))
  | is_TmemR_JS (NN n) = ag_TmemR gamma (ex_TmemR (NN n))
  | is_Tcond_JS (NN n) = ag_Tcond gamma (ex_Tcond (NN n))
  | is_TvarD_JS (NN n) = ag_TvarD gamma (ex_TvarD (NN n))
  | is_TfunD_JS (NN n) = ag_TfunD gamma (ex_TfunD (NN n))
  | is_TobjD_JS (NN n) = ag_TobjD gamma (ex_TobjD (NN n))
  | is_TWhile_JS (NN n) = ag_TWhile gamma (ex_TWhile (NN n))
  | is_BoolResOp_JS (NN n) = ag_BinOp gamma (ex_BinOp_JS (NN n)) JST0P_Bool
  | is_IntOp_JS (NN n) = ag_BinOp gamma (ex_BinOp_JS (NN n)) JST0P_Int
  | is_BoolOp_JS (NN n) = ag_BinOp gamma (ex_BinOp_JS (NN n)) JST0P_Bool
  | is_StringD_JS (NN n) = ag_StringD gamma (ex_StringD_JS (NN n))
ag_JSNode gamma (NT n _l _c) = ag_JSNode gamma (NN n)
ag_JSNode (a,b,g,n,_sol) j | trace 1 ("AG: Not handled " ++ show j) True = (a,b,JST0P_None,n,g,[])

ag_JSNode_list :: Con_in -> [JSNode] -> (Int,Int,[TypeP],Annotation, ContextAn,[ConstrainAn])
ag_JSNode_list (a,b,g,n,_sol) [] = (a,b,[],n,g,[])
ag_JSNode_list (a,b,g,n,sol) (j:js) | is_irrellevant_JS j = (ag_JSNode_list (a,b,g,n,sol) js)
                                    | otherwise = let
  (a1,b1,t1,n1,g1,c1) = ag_JSNode (a,b,g,n,sol) j
  (a2,b2,t2,n2,g2,c2) = ag_JSNode_list (a1,b1,g1,n1,sol) js
  in (a2,b2,t1:t2,n2,g2,concat [c1,c2])

--ag_Node :: Con_in -> Node -> Con_out
--ag_Node gamma (JSSourceElementsTop js) = ag_JSNodes gamma js
--ag_Node gamma (JSExpression js) = ag_JSNodes gamma js
--ag_Node (a,b,g,n,_sol) _ = (a,b,JST0P_None,n,g,[])

ag_JSNodes :: Con_in -> [JSNode] -> Con_out
ag_JSNodes gamma js | is_TvarW_JS js = ag_TvarW gamma (ex_TvarW js)
                    | is_TmemW1_JS js = ag_TmemW1 gamma (ex_TmemW1 js)
                    | is_TmemW2_JS js = ag_TmemW2 gamma (ex_TmemW2 js)
                    | is_TmemX_JS js = ag_TmemX gamma (ex_TmemX js)
                    | is_TfunX_JS js = ag_TfunX gamma (ex_TfunX js)
                    | is_TnewX_JS js = ag_TfunX gamma (ex_TnewX js)
ag_JSNodes (a,b,g,n,_sol) [] = (a,b,JST0P_None,n, g, [])
ag_JSNodes gamma [x] = ag_JSNode gamma x
ag_JSNodes gamma (x:xs) = ag_TSeq gamma [x] xs

----------------------------------------
-- Rules for constraint generation
----------------------------------------

ag_Tnull :: Con_in -> Con_out
ag_Tnull (a,b,g,n,sol) = let
  -- get solution for variables
  o = solutionP_get sol a
  a0 = a + 1
  -- We don't care about the resources in the null-type, since access to those results in a runtime error anyway, so there is no 
  -- evaluation for programs who try to access them.
  in (a0,b,o,n,g,[])

ag_TInt :: Con_in -> Con_out
ag_TInt (a,b,g,n,_sol) = let
  in (a,b,JST0P_Int,n,g,[])--[Gt [n] [n]])

ag_TvarR :: Con_in -> String -> Con_out
ag_TvarR (a,b,g,n,sol) var = let
  -- create now ResTV
  npost = N b
  n2 = N (b+1)
  b1 = b+2
  -- get solutions to the TVs
  t1 = solutionP_get sol a
  t2 = solutionP_get sol (a+1)
  a0 = a+2
  -- infer type
  ((t,n1),Definite) = var_get g var
  g1 = var_set g var ((t1,n2),Definite)
  c_split = makeSplit_P t1 t2 t
  c = [ Gt [npost,n2,c_varR] [n,n1],
        Gt [n,n1] [npost,n2,c_varR]]
  in (a0,b1,t2,npost,g1,concat[c,c_split])

ag_TvarW :: Con_in -> (String,[JSNode]) -> Con_out
ag_TvarW (a,b,g,n,sol) (x,e) = let
  -- create new ResTV
  ne = N b
  nxp = N (b+1)
  npost = N (b+2)
  b0 = b+3
  -- get solutions to the TVs
  txp = solutionP_get sol a
  a0 = a + 1
  -- infer types
  ((tx,nx),_psi) = var_get g x
  (a1,b1,te,nep,g1,c_1) = ag_JSNodes (a0,b0,g,ne,sol) e
  gp = var_set g1 x ((txp,nxp),Definite)
  -- constraints
  c_xe = makeEqual_P txp te
  c = [ Gt [n,nx] [ne],
        Gt [npost,nxp,c_varW] [nep],
        Gt [nep] [npost,nxp,c_varW]]
  in (a1,b1,te,npost,gp,concat[c_1,c,c_xe])

ag_TmemR :: Con_in -> ([JSNode],String) -> Con_out
ag_TmemR (a,b,g,n,sol) (e,m) = let
  -- create new ResTV
  npost = N b
  a0 = a+1
  -- infer type
  (a1,b1,o,n1p,g1,c_1) = ag_JSNodes (a0,b+1,g,n,sol) e
  ((t2,n2),Definite) = objectP_get o m
  c = [Gt [npost,c_memR] [n1p,n2],
       Gt [n1p,n2] [npost,c_memR]]
  in (a1,b1,t2,npost,g1,concat [c_1,c])

ag_TmemW1 :: Con_in -> (String,String,JSNode) -> Con_out
ag_TmemW1 (a,b,g,n,sol) (var,m,e) | trace 10 ("Ann-TmemW1 " ++ (show a) ++ " " ++ var ++ "." ++ m) False = undefined
ag_TmemW1 (a,b,g,n,sol) (var,m,e) = let
  -- create new ResTVs
  n1 = N b
  n2p = N (b+1)
  npost = N (b+2)
  b0 = b+3
  -- get solutions to TVs
  op = solutionP_get sol (a+1)
  a0 = a + 3
  -- infer type
  ((o,n2),_psi) = var_get g1 var
  (a1,b1,te,n1p,g1,c_1) = ag_JSNode (a0,b0,g,n1,sol) e
  ((_,n3pot ),psi) = objectP_get o m
  n3 | psi == Definite = n3pot
     | otherwise = I 0
  ((_,n3p),Definite) = objectP_get op (m)
  g2 = var_set g1 var ((op,n2p),Definite)
  
  c = [Gt [n,n2] [n1],
       Gt [npost,n3p,n2p,c_memW psi] [n1p,n3],
       Gt [n1p,n3] [npost,n3p,n2p,c_memW psi]]
  in (a1,b1,te,npost,g2,concat [c_1,c])

ag_TmemW2 :: Con_in -> ([JSNode],String,JSNode) -> Con_out
ag_TmemW2 (a,b,g,n,sol) (e1,m,e2) = let
  -- create new ResTV
  npost = N b
  b0 = b+1
  a0 = a+1
  -- infer type
  (a1,b1,o ,n1p,g1,c_1) = ag_JSNodes (a0,b0,g,n,sol) e1
  (a2,b2,t2,n2p,g2,c_2) = ag_JSNode (a1,b1,g1,n1p,sol) e2
  ((_tm,n3),Definite) = objectP_get o m
  c = [Gt [npost,c_memW Definite] [n2p,n3],
       Gt [n2p,n3] [npost,c_memW Definite]]
  in (a2,b2,t2,npost,g2,concat [c_1,c_2,c])

ag_TmemX :: Con_in -> ([JSNode],String,[JSNode]) -> Con_out
ag_TmemX (a,b,gamma,n,sol) (e,m,ei) = let
  -- aquire new annotation variables
  n1 = N b
  npost = N (b+1)
  a0 = a+3
  a1 = ag_ArgList_copy a0 ei
  -- infer function type
  (a2,b2,te,nep,g1,c_e) = ag_JSNodes (a1,b+2,gamma,n1,sol) e
  ((g,ng),Definite) = objectP_get te m
  (JST0P_Function o tx nf tp nfp) = g
  c_n1 = [Gt [n1] [nep,ng],Gt [nep,ng] [n1]]
  -- infer argument type
  (a3,b3,ti,n2,g2,c_ei) = ag_JSNode_list (a2,b2,g1,n1,sol) ei
  c =[Gt [npost,c_funX,nf] [n2,nfp],
      Gt [n2,nfp] [npost,c_funX,nf]]
  c_g = makeEqual_P g (JST0P_Function o tx nf tp nfp)
  c_o = makeMore_P te o
  c_ti = makeMore_list ti tx
  in (a3,b3,tp,npost,g2,concat[c,c_n1,c_g,c_ti,c_o,c_e,c_ei])

ag_TfunX :: Con_in -> (String,[JSNode]) -> Con_out
ag_TfunX (a,b,gamma,n,sol) (f,ei) = let
  -- create new annotation variables
  ngp = N b
  n1 = N (b+1)
  np = N (b+2)
  a0 = a+2
  a2 = ag_ArgList_copy a0 ei
  --infer function type
  ((g,ng),Definite) = var_get gamma f
  g1 = var_set gamma f ((g,ngp),Definite)
  -- infer argument types
  (a4,b4,ti,n2,g2,c_ei) = ag_JSNode_list (a2,b+3,g1,n1,sol) ei
  (JST0P_Function o tx nf tp nfp) = g

  c = [ Gt [n,ng] [n1,ngp],
        Gt [n2] [nf,c_funX],
        Gt [np,c_funX,nf] [n2,nfp],
        Gt [n2,nfp] [np,c_funX,nf]]
  c_o = makeEmpty_P o
  c_ti = makeMore_list ti tx
  in (a4,b4,tp,np,g2,concat[c_ti,c_o,c_ei,c])

ag_TSeq :: Con_in -> [JSNode] -> [JSNode] -> Con_out
ag_TSeq (a,b,g,n,sol) e1 e2 | is_irrellevant_list e1 = ag_JSNodes (a,b,g,n,sol) e2
                            | is_irrellevant_list e2 = ag_JSNodes (a,b,g,n,sol) e1
                            | otherwise = let
                              -- create new ResTV
                              npost = N b
                              -- infer type
                              (a1,b1,_t1,n1,g1,c_1) = ag_JSNodes (a,b+1,g,n,sol) e1
                              (a2,b2,t2,n2,g2,c_2) = ag_JSNodes (a1,b1,g1,n1,sol) e2
                              c = [Gt [npost,c_seq] [n2],
                                   Gt [n2] [npost,c_seq]]
                              in (a2,b2,t2,n2,g2,concat [c_1,c_2,c])


ag_Tcond :: Con_in -> (JSNode,[JSNode],[JSNode]) -> Con_out
ag_Tcond (a,b,g,n,sol) (e1,e2,e3) = let
  -- create new variables
  npost = N b
  -- get solution for TVs
  t = solutionP_get sol a
  a0 = a+1
  -- infer type
  (a1,b1,_tb,n1p,g1,c_1) = ag_JSNode (a,b+1,g,n,sol) e1
  (a2,b2,_tt,n2p,g2,c_2) = ag_JSNodes (a1,b1,g1,n1p,sol) e2
  (a3,b3,_tf,n3p,g3,c_3) = ag_JSNodes (a2,b2,g1,n1p,sol) e3
  c = [Gt [n2p] [npost],
       Gt [n3p] [npost]]
  (c_G,gammar,a4,b4) = context_min_constrain g2 g3 (a3,b3)
  in (a4,b4,t,npost,gammar,concat [c,c_1,c_2,c_3,c_G])

ag_TvarD :: Con_in -> (String,JSNode) -> Con_out
ag_TvarD (a,b,g,n,sol) (var,e) = ag_JSNode (a,b,g,n,sol) e

ag_TfunD :: Con_in -> (String,[String],JSNode) -> Con_out
ag_TfunD (a,b,gamma,n,sol) (f,xi,e) = let
  -- define variables
  ne = N(b)
  nf = N (b+1)
  b1 = b + 2
  -- get solutions for TVs
  tThis = solutionP_get sol a
  a0 = a+1
  (a1,tx) = ag_ArgList a0 xi sol
  --ne1 = c_mult c_varD (Prelude.length xi)
  -- prepare contexts
  ((tf,nsf),_psi) | f == ""   = ((JST0P_Function tThis tx nf te nep,I 0),Definite)
                  | otherwise = var_get gamma f
  gammap | f == "" = gamma
         | otherwise = var_set gamma f ((tf,nsf),Definite)
  gfp = var_set_list gammap ("this":xi) (list2DefAn (tThis:tx))
  -- infer function body
  (a2,b2,gf,ne1) = fpp_JSNode (a1,b1,sol,gfp) e
  (a3,b3,te,nep,g1,c_1) = ag_JSNode (a2,b2,gf,ne,sol) e
  -- put together results
  c_tf | f == ""   = []
       | otherwise = makeEqual_P tf (JST0P_Function tThis tx nf te nep)
  c = [Gt [nf] [ne,I ne1]]
  in (a3,b3,tf,n,gammap,concat [c_tf,c,c_1])

ag_TobjD :: Con_in -> [(String,[JSNode])] -> Con_out
ag_TobjD (a,b,g,n,sol) fields = let
  -- create TVs
  np = N b
  b0 = b+1
  -- get solutions to TVs
  o = solutionP_get sol a
  a0 = a+1
  -- infer type
  (a1,b1,types,n1,gp,c_1) = ag_fields (a0,b0,g,n,sol) fields
  to = objectP_from_list NotRec types
  c_o = makeEqual_P o to
  c = [Gt [n1] [np,c_objD],
       Gt [np,c_objD] [n1]]
  in (a1,b1,o,np,gp,concat[c,c_1,c_o])

ag_TWhile :: Con_in -> (JSNode,JSNode) -> Con_out
ag_TWhile (a,b,g,n,sol) (bool,e) = let
  -- create variables
  np = N b
  b0 = b+1
  a0 = a
  -- infer types
  (a1,b1,_tb,n1,g1,c_1) = ag_JSNode (a0,b0,g,n,sol) bool
  (a2,b2,_te,n2,g2,c_2) = ag_JSNode (a1,b1,g1,n1,sol) e
  c_g = context_sub_constrain g2 g1
  c = [Gt [n2] [n1], Gt [n1] [np], Gt [n2] [np]]
  in (a2,b2,JST0P_None,np,g1,concat [c,c_1,c_2,c_g])

ag_BinOp :: Con_in -> ([JSNode],[JSNode]) -> TypeP -> Con_out
ag_BinOp (a,b,g,n,sol) (e1,e2) t = let
  (a1,b1,_t1,n1,g1,c_1) = ag_JSNodes (a,b,g,n,sol) e1
  (a2,b2,_t2,n2,g2,c_2) = ag_JSNodes (a1,b1,g1,n1,sol) e2
  in (a2,b2,t,n2,g2,concat [c_1,c_2])

ag_StringD :: Con_in -> String -> Con_out
ag_StringD (a,b,g,n,sol) s =
  (a,b,JST0P_String "",n,g,[])

----------------------------------------
-- Auxiliary Functions
----------------------------------------

list2DefAn :: [TypeP] -> [(TypeAn,FieldType)]
list2DefAn = Prelude.map (\t->((t,I 0),Definite))

ag_fields :: Con_in -> [(String,[JSNode])] -> (Int,Int,[(String,TypeAn)],Annotation,ContextAn,[ConstrainAn])
ag_fields (a,b,g,n,_sol) [] = (a,b,[],n,g,[])
ag_fields (a,b,g,n,sol) ((s,js):jx) = let
  (as,bs,ts,ns,gs,c_s) = ag_JSNodes (a,b,g,n,sol) js
  nts = N bs
  (ax,bx,l ,nx,gx,c_x) = ag_fields (as,bs+1,gs,ns,sol) jx
  np = N bx
  c = [Gt [np,nts,c_memW Potential] [nx],
       Gt [nx] [np,nts,c_memW Potential]]
  in (ax,bx+1,(s,(ts,nts)):l,np,gx,concat[c,c_s,c_x])

ag_ArgList_copy :: Int -> [a] -> Int
ag_ArgList_copy a xs = a + (Prelude.length xs)

ag_ArgList :: Int -> [String] -> SolutionP -> (Int,[TypeP])
ag_ArgList a [] _sol = (a,[])
ag_ArgList a (_x:xs) sol = let --name of argument has already been analysed by cg
  tx = solutionP_get sol a
  (as,txs) = ag_ArgList (a+1) xs sol
  in (as,tx:txs)
              
----------------------------------------
-- First pass
----------------------------------------

type FPP_in = (Int,Int,SolutionP,ContextAn)
type FPP_out = (Int,Int,ContextAn,Int)

in2out :: FPP_in -> Int -> FPP_out
in2out (a,b,_sol,gamma) i = (a,b,gamma,i)

out2in :: FPP_out -> SolutionP -> FPP_in
out2in (a,b,gamma,_i) sol = (a,b,sol,gamma)

fpp_JSNode :: FPP_in -> JSNode -> FPP_out
fpp_JSNode _g j | trace 30 ("\nfpp_JSNode : " ++ (show j)) False = undefined
fpp_JSNode g (NN (JSSourceElementsTop js)) = fpp_JSNodes g js
fpp_JSNode g (NN (JSLiteral "")) = in2out g 0
fpp_JSNode g (NN (JSExpression js)) = fpp_JSNodes g js
fpp_JSNode g (NN (JSVariables _var js _cont)) = fpp_JSNodes g js
fpp_JSNode g (NN (JSBlock _rb js _lb)) = fpp_JSNodes g js
fpp_JSNode g (NN (JSExpressionParen _rb j _lb)) = fpp_JSNode g j
fpp_JSNode g (NN n)
  | is_Tnull_JS (NN n) = in2out g 0
  | is_TInt_JS (NN n) = in2out g 0
  | is_TvarR_JS (NN n) = in2out g 0
  | is_TmemR_JS (NN n) = fpp_TmemR g (ex_TmemR (NN n))
  | is_Tcond_JS (NN n) = fpp_Tcond g (ex_Tcond (NN n))
  | is_TfunD_JS (NN n) = fpp_TfunD g (ex_TfunD (NN n))
  | is_TobjD_JS (NN n) = fpp_TobjD g (ex_TobjD (NN n))
  | is_TvarD_JS (NN n) = fpp_TvarD g (ex_TvarD (NN n))
  | is_TWhile_JS (NN n) = fpp_TWhile g (ex_TWhile (NN n))
  | is_BoolResOp_JS (NN n) = fpp_BinOp g (ex_BinOp_JS (NN n))
  | is_IntOp_JS (NN n) = fpp_BinOp g (ex_BinOp_JS (NN n))
  | is_BoolOp_JS (NN n) = fpp_BinOp g (ex_BinOp_JS (NN n))
  | is_StringD_JS (NN n) = fpp_StringD g (ex_StringD_JS (NN n))
fpp_JSNode g (NT n _l _c) = fpp_JSNode g (NN n)
fpp_JSNode (a,b,_sol,gamma) j | trace 1 ("FPP: Expression not handled" ++ show j) True = (a,b,gamma,0)
                              | True = undefined

fpp_JSNodes :: FPP_in -> [JSNode] -> FPP_out
fpp_JSNodes g js
  | is_TvarW_JS js = fpp_TvarW g (ex_TvarW js)
  | is_TmemW1_JS js = fpp_TmemW1 g (ex_TmemW1 js)
  | is_TmemW2_JS js = fpp_TmemW2 g (ex_TmemW2 js)
  | is_TmemX_JS js = fpp_TmemX g (ex_TmemX js)
  | is_TfunX_JS js = fpp_TfunX g (ex_TfunX js)
  | is_TnewX_JS js = fpp_TfunX g (ex_TnewX js)
fpp_JSNodes g [] = in2out g 0
fpp_JSNodes g [x] = fpp_JSNode g x
fpp_JSNodes g (x:xs) = fpp_TSeq g [x] xs

fpp_TvarW :: FPP_in -> (String,[JSNode]) -> FPP_out
fpp_TvarW g (_x,e) = fpp_JSNodes g e

fpp_TmemR :: FPP_in -> ([JSNode],String) -> FPP_out
fpp_TmemR g (e,_m) = fpp_JSNodes g e

fpp_TmemW1 :: FPP_in -> (String,String,JSNode) -> FPP_out
fpp_TmemW1 g (_var,_m,e) = fpp_JSNode g e

fpp_TmemW2 :: FPP_in -> ([JSNode],String,JSNode) -> FPP_out
fpp_TmemW2 (a,b,sol,gamma) (e1,_m,e2) = let
  (a1,b1,gamma1,n1) = fpp_JSNodes (a,b,sol,gamma) e1
  (a2,b2,gamma2,n2) = fpp_JSNode (a1,b1,sol,gamma1) e2
  in (a2,b2,gamma2,n1+n2)

fpp_TmemX :: FPP_in -> ([JSNode],String,[JSNode]) -> FPP_out
fpp_TmemX (a,b,sol,gamma) (e1,m,e2) = let
  (a1,b1,gamma1,n1) = fpp_JSNodes (a,b,sol,gamma) e1
  (a2,b2,gamma2,n2) = fpp_JSNodes (a1,b1,sol,gamma1) e2
  in (a2,b2,gamma2,n1+n2)

fpp_TfunX :: FPP_in -> (String,[JSNode]) -> FPP_out
fpp_TfunX g (f,e) = fpp_JSNodes g e

fpp_TSeq :: FPP_in -> [JSNode] -> [JSNode] -> FPP_out
fpp_TSeq g e1 e2 | is_irrellevant_list e1 = fpp_JSNodes g e2
                 | is_irrellevant_list e2 = fpp_JSNodes g e1
                 | otherwise = let
                   (a,b,sol,gamm) = g
                   (a1,b1,g1,r1) = fpp_JSNodes g e1
                   (a2,b2,g2,r2) = fpp_JSNodes (a1,b1,sol,g1) e2
                   in (a2,b2,g2,r1+r2)

fpp_Tcond :: FPP_in -> (JSNode,[JSNode],[JSNode]) -> FPP_out
fpp_Tcond (a,b,sol,gamma) (e1,e2,e3) = let
  (a1,b1,g1,r1) = fpp_JSNode  (a ,b ,sol,gamma) e1
  (a2,b2,g2,r2) = fpp_JSNodes (a1,b1,sol,g1) e2
  (a3,b3,g3,r3) = fpp_JSNodes (a2,b2,sol,g2) e3
  in (a3,b3,g3,r1+r2+r3)

fpp_TvarD :: FPP_in -> (String,JSNode) -> FPP_out
fpp_TvarD (a,b,sol,gamma) (var,e) = let
  tvar = solutionP_get sol a --JST0_TV a (var ++ "Decl")
  nvar = N b
  gammap = var_set gamma var ((tvar,nvar),Potential)
  (ap,bp,gp,ip) = fpp_JSNode (a+1,b+1,sol,gammap) e
  in (ap,bp,gp,ip+c_varDi)

fpp_TfunD :: FPP_in -> (String,[String],JSNode) -> FPP_out
fpp_TfunD (a,b,sol,gamma) (f,_x,_e) | f == "" = (a,b,gamma,1)
                                    |otherwise = let
  tf = solutionP_get sol a --JST0_TV a (f++"Decl")
  gammap = var_set gamma f ((tf,I 0),Definite)
  in (a+1,b+1,gammap,c_funDi)

fpp_TobjD :: FPP_in -> [(String,[JSNode])] -> FPP_out
fpp_TobjD g [] = in2out g 0
fpp_TobjD (a,b,sol,gamma) ((_s,js):jx) =
  fpp_TobjD (out2in (fpp_JSNodes (a,b,sol,gamma) js) sol) jx

fpp_TWhile :: FPP_in -> (JSNode,JSNode) -> FPP_out
fpp_TWhile (a,b,sol,gamma) (bool, e) = fpp_TSeq (a,b,sol,gamma) [bool] [e]

fpp_BinOp :: FPP_in -> ([JSNode],[JSNode]) -> FPP_out
fpp_BinOp (a,b,sol,gamma) (e1,e2) = fpp_TSeq (a,b,sol,gamma) e1 e2

fpp_StringD :: FPP_in -> String -> FPP_out
fpp_StringD (a,b,_sol,gamma) _s = (a,b,gamma,0)
