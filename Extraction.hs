module Extraction (
  ex_code,
  ex_code_list,
  ex_TvarR,
  ex_TvarW,
  ex_TmemR,
  ex_TmemW1,
  ex_TmemW2,
  ex_TmemX,
  ex_TfunX,
  ex_TnewX,
  ex_Tcond,
  ex_TvarD,
  ex_TfunD,
  ex_TobjD,
  ex_TWhile,
  ex_BinOp_JS,
  ex_StringD_JS
  ) where

import Language.JavaScript.Parser.AST

import Conditionals

import Debugging

----------------------------------------
-- Extractions for the rules
----------------------------------------

ex_TvarR :: JSNode -> String
ex_TvarR _ | trace 30 "ex_TvarR" False = undefined
ex_TvarR j = ex_var_name_JS j

ex_TvarW :: [JSNode] -> (String, [JSNode])
ex_TvarW js | trace 30 ("ex_TvarW " ++ show js) False = undefined
ex_TvarW (var:(_op:e)) = (ex_var_name_JS var,e)
ex_TvarW _ = undefined

ex_TmemR :: JSNode -> ([JSNode], String)
ex_TmemR _ | trace 30 "ex_TmemR" False = undefined
ex_TmemR j = (ex_obj_JS j,ex_field_JS j)

ex_TmemW1 :: [JSNode] -> (String, String, JSNode)
ex_TmemW1 _ | trace 30 "ex_TmemW1" False = undefined
ex_TmemW1 [obj,_op,e] = let
  (var,m) = ex_field_of_var_JS obj
  in (var,m,e)
ex_TmemW1 _ = undefined

ex_TmemW2 :: [JSNode] -> ([JSNode], String, JSNode)
ex_TmemW2 _ | trace 30 "ex_TmemW2" False = undefined
ex_TmemW2 [obj,_op,e] = (ex_obj_JS obj,ex_field_JS obj,e)
ex_TmemW2 _ = undefined 

ex_TmemX :: [JSNode] -> ([JSNode], String, [JSNode])
ex_TmemX _ | trace 30 "ex_TmemX" False = undefined
ex_TmemX [obj,args] = (ex_obj_JS obj,ex_field_JS obj,ex_args_JS args)
ex_TmemX _ = undefined

ex_TfunX :: [JSNode] -> (String,[JSNode])
ex_TfunX _ | trace 30 "ex_TfunX" False = undefined
ex_TfunX [f,args] = (ex_var_name_JS f,ex_args_JS args)
ex_TfunX _ = undefined

ex_TnewX :: [JSNode] -> (String,[JSNode])
ex_TnewX _ | trace 30 "ex_TnewX" False = undefined
ex_TnewX [_new,f,args] = (ex_var_name_JS f,ex_args_JS args)
ex_TnewX _ = undefined 

ex_Tcond :: JSNode -> (JSNode,[JSNode],[JSNode])
ex_Tcond _ | trace 30 "ex_Tcond" False = undefined
ex_Tcond j = ex_if_comps_JS j

ex_TvarD :: JSNode -> (String,JSNode)
ex_TvarD j | trace 30 ("ex_TvarD: " ++ show j) False = undefined
ex_TvarD j = ex_decl_comps_JS j

ex_TfunD :: JSNode -> (String,[String],JSNode)
ex_TfunD _ | trace 30 "ex_TfunD: " False = undefined
ex_TfunD j = ex_fun_comps_JS j

ex_TobjD :: JSNode -> [(String,[JSNode])]
ex_TobjD _ | trace 30 "ex_TobjD" False = undefined
ex_TobjD j = ex_objDecl_JS j

ex_TWhile :: JSNode -> (JSNode, JSNode)
ex_TWhile _ | trace 30 "ex_TWhile" False = undefined
ex_TWhile j = (extract_JSNode ex_while) j
----------------------------------------
-- component extractors
----------------------------------------

ex_BinOp_JS :: JSNode -> ([JSNode],[JSNode])
ex_BinOp_JS _ | trace 30 "ex_BinOp" False = undefined
ex_BinOp_JS j = (extract_JSNode ex_binop) j

ex_binop :: Node -> ([JSNode],[JSNode])
ex_binop (JSExpressionBinary _s e1 _op e2) = (e1,e2)
ex_binop _ = undefined

ex_var_name :: Node -> String
ex_var_name n | trace 30 ("ex_var_name " ++ (show n)) False = undefined
ex_var_name (JSIdentifier s) = s
ex_var_name (JSLiteral "this") = "this"
ex_var_name _ = undefined

ex_var_name_JS :: JSNode -> String
ex_var_name_JS = extract_JSNode ex_var_name

ex_var_name_list :: [JSNode] -> [String]
ex_var_name_list [] = []
ex_var_name_list (x:xs) | is_irrellevant_JS x = ex_var_name_list xs
                        | otherwise = (ex_var_name_JS x):(ex_var_name_list xs)

ex_obj :: Node -> [JSNode]
ex_obj (JSMemberDot ps _dot _field) = ps
ex_obj (JSMemberSquare ps _lb _field _rb) = ps
ex_obj _ = undefined

ex_obj_JS :: JSNode -> [JSNode]
ex_obj_JS = extract_JSNode ex_obj

ex_field :: Node -> String
ex_field (JSMemberDot _ps _dot field) = ex_var_name_JS field
ex_field (JSMemberSquare _ps _lb field _rb) = ex_var_name_JS field
ex_field _ = undefined

ex_field_JS :: JSNode -> String
ex_field_JS = extract_JSNode ex_field

ex_field_of_var :: Node -> (String,String)
ex_field_of_var (JSMemberDot [o] _dot field) = (ex_var_name_JS o, ex_var_name_JS field)
ex_field_of_var _ = undefined 

ex_field_of_var_JS :: JSNode -> (String,String)
ex_field_of_var_JS = extract_JSNode ex_field_of_var

ex_args :: Node -> [JSNode]
ex_args (JSArguments _lb args _rb) = args
ex_args _ = undefined 

ex_args_JS :: JSNode -> [JSNode]
ex_args_JS = extract_JSNode ex_args

ex_if_comps :: Node -> (JSNode, [JSNode],[JSNode])
ex_if_comps (JSIf _if _lb bool _rb true cont) = (bool,true,cont)
ex_if_comps _ = undefined 

ex_if_comps_JS :: JSNode -> (JSNode, [JSNode], [JSNode])
ex_if_comps_JS = extract_JSNode ex_if_comps

ex_decl_comps :: Node -> (String,JSNode)
ex_decl_comps j | trace 30 ("ex_decl_comps: " ++ show j) False = undefined
ex_decl_comps (JSVarDecl x d) = let ds = ex_varDecl d
                                in case ds of
                                  [] -> (ex_var_name_JS x,NN (JSExpression []))
                                  _ -> (ex_var_name_JS x,NN (JSExpression (x:ds)))
ex_decl_comps _ = undefined 

ex_decl_comps_JS :: JSNode -> (String,JSNode)
ex_decl_comps_JS = extract_JSNode ex_decl_comps

ex_fun_comps :: Node -> (String,[String],JSNode)
ex_fun_comps (JSFunction _function f _lb args _rb e) = (ex_var_name_JS f,ex_var_name_list args,e)
ex_fun_comps (JSFunctionExpression _function _ _lb args _rb e) = ("",ex_var_name_list args,e)
ex_fun_comps _ = undefined 

ex_fun_comps_JS :: JSNode -> (String,[String],JSNode)
ex_fun_comps_JS = extract_JSNode ex_fun_comps

ex_varDecl :: [JSNode] -> [JSNode]
ex_varDecl js | trace 30 ("ex_varDecl: " ++ show js) False = undefined
ex_varDecl (o:es) | trace 30 ("ex_varDecl: " ++ show o) True = ((NN (JSOperator o))):es
ex_varDecl [] | trace 30 "ex_varDecl: emty" True = []
ex_varDecl _ = undefined 

ex_objDecl :: Node -> [(String,[JSNode])]
ex_objDecl (JSObjectLiteral _lb fields _rb) = ex_fieldList fields
ex_objDecl _ = undefined 

ex_objDecl_JS :: JSNode -> [(String,[JSNode])]
ex_objDecl_JS = extract_JSNode ex_objDecl

ex_fieldList :: [JSNode] -> [(String,[JSNode])]
ex_fieldList [] =[]
ex_fieldList (x:xs) = case x of
  (NT (JSLiteral ",") _p _c) -> ex_fieldList xs
  _ -> (ex_fieldDecl_JS x):(ex_fieldList xs)

ex_fieldDecl :: Node -> (String,[JSNode])
ex_fieldDecl j | trace 30 ("\nex_fieldDecl : " ++ (show j)) False = undefined
ex_fieldDecl (JSPropertyNameandValue a _dev e) = (ex_String_JS a,e)
ex_fieldDecl _ = undefined 

ex_fieldDecl_JS :: JSNode -> (String,[JSNode])
ex_fieldDecl_JS = extract_JSNode ex_fieldDecl

ex_string :: Node -> String
ex_string (JSStringLiteral _lim s) =s
ex_string (JSIdentifier s) = s
ex_string _ = undefined 

ex_String_JS :: JSNode -> String
ex_String_JS = extract_JSNode ex_string

ex_StringD_JS :: JSNode -> String
ex_StringD_JS = extract_JSNode ex_stringD

ex_stringD :: Node -> String
ex_stringD (JSStringLiteral _lim s) = s
ex_stringD _ = undefined

ex_while :: Node -> (JSNode,JSNode)
ex_while (JSWhile _while _rb bool _lb e) = (bool,e)
ex_while _ = undefined 

----------------------------------------
-- Meta functions
----------------------------------------

extract_JSNode :: (Node -> t) -> JSNode -> t
extract_JSNode f (NN n) = f n
extract_JSNode f (NT n _p _c) = extract_JSNode f (NN n)

-- extract the path to a field of a 
ex_path_List :: [JSNode] -> String
ex_path_List [x] = ex_path_JS x
ex_path_List (_:xs) = ex_path_List xs
ex_path_List [] = ""

ex_path_JS :: JSNode -> String
ex_path_JS (NN n) = ex_path n
ex_path_JS (NT n _ _) = ex_path n

ex_path :: Node -> String
ex_path (JSIdentifier s) = s
ex_path (JSMemberDot objs _sep field) = ex_path_List objs ++ "." ++ ex_path_JS field
ex_path (JSMemberSquare objs _lb field _rb) = ex_path (JSMemberDot objs _lb field)

--ex_TfunX_list :: [JSNode] -> (String, [JSNode])
--ex_TfunX_list (e:_es) = ex_TfunX_JS e

--ex_TfunX_JS :: JSNode -> (String, [JSNode])
--ex_TfunX_JS (NN n) = ex_TfunX n
--ex_TfunX_JS (NT n _ _) = ex_TfunX_JS (NN n)

--ex_TfunX :: Node -> (String, [JSNode])
--ex_TfunX (JSExpression [e1,e2]) = (ex_fname_JS e1,ex_arg_JS e2)

ex_code :: JSNode -> String
ex_code = ss

ex_code_list :: [JSNode] -> String
ex_code_list [] = ""
ex_code_list (x:xs) = ex_code x ++ ex_code_list xs

ss :: JSNode -> String
ss (NN node    ) = showCode node
ss (NT node _ _) = showCode node

sss :: [JSNode] -> String
sss xs = (concatMap ss xs)

showCode :: Node -> String
showCode (JSArguments lb xs rb) = ss lb ++ sss xs ++ ss rb
showCode (JSArrayLiteral lb xs rb) = ss lb ++ sss xs ++ ss rb
showCode (JSBlock lb xs rb) = sss lb ++ sss xs ++ sss rb
showCode (JSBreak b x1s as) =  ss b ++ sss x1s ++ ss as
showCode (JSCallExpression _s os xs cs) = sss os ++ sss xs ++ sss cs
showCode (JSCase ca x1 c x2s) = ss ca ++ ss x1 ++ ss c ++ sss x2s
showCode (JSCatch c lb x1 x2s rb x3) = ss c ++ ss lb ++ ss x1 ++ sss x2s ++ ss rb ++ ss x3
showCode (JSContinue c xs as) = ss c ++ sss xs ++ ss as
showCode (JSDecimal s) = show s
showCode (JSDefault d c xs) = ss d ++ ss c ++ sss xs
showCode (JSDoWhile d x1 w lb x2 rb x3) = ss d ++ ss x1 ++ ss w ++ ss lb ++ ss x2 ++ ss rb ++ ss x3
showCode (JSElision c) = ss c
showCode (JSExpression xs) = sss xs
showCode (JSExpressionBinary s x2s op x3s) = show s ++ sss x2s ++ ss op ++ sss x3s
showCode (JSExpressionParen lp x rp) = ss lp ++ ss x ++ ss rp
showCode (JSExpressionPostfix s xs op) = show s ++ sss xs ++ ss op
showCode (JSExpressionTernary x1s q x2s c x3s) = sss x1s ++ ss q ++ sss x2s ++ ss c ++ sss x3s
showCode (JSFinally f x) = ss f ++ ss x
showCode (JSFor f lb x1s s1 x2s s2 x3s rb x4) = ss f ++ ss lb ++ sss x1s ++ ss s1 ++ sss x2s ++ ss s2 ++ sss x3s ++ show rb ++ ss x4 ++ ss lb
showCode (JSForIn f lb x1s i x2 rb x3) = ss f ++ ss lb ++ sss x1s ++ ss i ++ ss x2 ++ ss rb ++ ss x3
showCode (JSForVar f lb v x1s s1 x2s s2 x3s rb x4) = ss f ++ ss lb ++ ss v ++ sss x1s ++ ss s1 ++ sss x2s ++ ss s2 ++ sss x3s ++ ss rb ++ ss x4
showCode (JSForVarIn f lb v x1 i x2 rb x3) = ss f ++ ss lb ++ ss v ++ ss x1 ++ ss i ++ ss x2 ++ ss rb ++ ss x3
showCode (JSFunction f x1 lb x2s rb x3) = ss f ++ ss x1 ++ ss lb ++ sss x2s ++ ss rb ++ ss x3
showCode (JSFunctionExpression f x1s lb x2s rb x3) = ss f ++ sss x1s ++ ss lb ++ sss x2s ++ ss rb ++ ss x3
showCode (JSHexInteger s) = show s
showCode (JSOctal s) = show s
showCode (JSIdentifier s) = show s
showCode (JSIf i lb x1 rb x2s x3s) = ss i ++ ss lb ++ ss x1 ++ ss rb ++ sss x2s ++ sss x3s
showCode (JSLabelled x1 c x2) = ss x1 ++ ss c ++ ss x2
showCode (JSLiteral s) = show s
showCode (JSMemberDot x1s d x2 ) = sss x1s ++ ss d  ++ ss x2
showCode (JSMemberSquare x1s lb x2 rb) = sss x1s ++ ss lb ++ ss x2 ++ ss rb
showCode (JSObjectLiteral lb xs rb) = ss lb ++ sss xs ++ ss rb
showCode (JSOperator n) = ss n
showCode (JSPropertyNameandValue x1 colon x2s) = ss x1 ++ ss colon ++ sss x2s
showCode (JSPropertyAccessor s x1 lb1 x2s rb1 x3) = show s ++ ss x1 ++ ss lb1 ++ sss x2s ++ ss rb1 ++ ss x3
showCode (JSRegEx s) = show s
showCode (JSReturn r xs as) = ss r ++ sss xs ++ ss as
showCode (JSSourceElementsTop xs) = sss xs
showCode (JSStringLiteral _c s) = show s
showCode (JSSwitch s lb x rb x2) = ss s ++ ss lb ++ ss x ++ ss rb ++ ss x2
showCode (JSThrow t x) = ss t ++ ss x
showCode (JSTry t x1 x2s) = ss t ++ ss x1 ++ sss x2s
showCode (JSUnary _s x) = show x
showCode (JSVarDecl x1 x2s) = ss x1 ++ sss x2s
showCode (JSVariables n xs as) = ss n ++ sss xs ++ ss as
showCode (JSWhile w lb x1 rb x2) = ss w ++ ss lb ++ ss x1 ++ ss rb ++ ss x2
showCode (JSWith w lb x1 rb x2s) = ss w ++ ss lb ++ ss x1 ++ ss rb ++ sss x2s


