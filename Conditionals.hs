module Conditionals where

import Language.JavaScript.Parser.AST
import Language.JavaScript.Parser.Parser

----------------------------------------
-- conditionals for the typing rules
----------------------------------------

is_Tnull :: Node -> Bool
is_Tnull (JSLiteral s) = (s == "null")
is_Tnull _ = False

is_Tnull_JS :: JSNode -> Bool
is_Tnull_JS = check_JSNode is_Tnull

is_TInt :: Node -> Bool
is_TInt (JSDecimal _i) = True
is_TInt _ = False

is_TInt_JS :: JSNode -> Bool
is_TInt_JS = check_JSNode is_TInt

is_TvarR_JS :: JSNode -> Bool
is_TvarR_JS = is_var_acc_JS

is_TvarW_JS :: [JSNode] -> Bool
is_TvarW_JS = check_JSNodes [is_var_acc_JS, is_assign_op_JS]

is_TmemR_JS :: JSNode -> Bool
is_TmemR_JS = is_obj_acc_JS

is_TmemW1_JS :: [JSNode] -> Bool
is_TmemW1_JS = check_JSNodes [is_field_of_var_JS, is_assign_op_JS]

is_TmemW2_JS :: [JSNode] -> Bool
is_TmemW2_JS = check_JSNodes [is_obj_acc_JS, is_assign_op_JS]

is_TmemX_JS :: [JSNode] -> Bool
is_TmemX_JS = check_JSNodes [is_obj_acc_JS, is_argument_JS]

is_TfunX_JS :: [JSNode] -> Bool
is_TfunX_JS = check_JSNodes [is_var_acc_JS, is_argument_JS]

is_TnewX_JS :: [JSNode] -> Bool
is_TnewX_JS = check_JSNodes [is_new_JS, is_JSNode, is_argument_JS] 

is_Tcond_JS :: JSNode -> Bool
is_Tcond_JS = is_if_JS

is_TvarD_JS :: JSNode -> Bool
is_TvarD_JS = is_VarDecl_JS

is_TfunD_JS :: JSNode -> Bool
is_TfunD_JS = is_funDecl_JS

is_TobjD_JS :: JSNode -> Bool
is_TobjD_JS = is_objDecl_JS

is_TWhile_JS :: JSNode -> Bool
is_TWhile_JS = check_JSNode is_while

is_StringD_JS :: JSNode -> Bool
is_StringD_JS = check_JSNode is_string

is_BoolResOp_JS :: JSNode -> Bool
is_BoolResOp_JS = check_JSNode is_boolresop

is_IntOp_JS :: JSNode -> Bool
is_IntOp_JS = check_JSNode is_intop

is_BoolOp_JS :: JSNode -> Bool
is_BoolOp_JS = check_JSNode is_boolop
----------------------------------------
-- Check for JSNodes
----------------------------------------

check_JSNode :: (Node -> Bool) -> JSNode -> Bool
check_JSNode f (NN n) = f n
check_JSNode f (NT n _ _) = check_JSNode f (NN n)

check_JSNodes :: [JSNode -> Bool] -> [JSNode] -> Bool
check_JSNodes [] _ = True
check_JSNodes (b:bs) (j:js) = (b j) && check_JSNodes bs js
check_JSNodes _ [] = False

is_JSNode :: JSNode -> Bool
is_JSNode _ = True

-- is the Node list a function call
is_irrellevant :: Node -> Bool
is_irrellevant (JSLiteral "") = True
is_irrellevant (JSLiteral ";") = True
is_irrellevant (JSLiteral ",") = True
is_irrellevant (JSLiteral "else") = True
is_irrellevant _ = False

is_irrellevant_JS :: JSNode -> Bool
is_irrellevant_JS = check_JSNode is_irrellevant

is_irrellevant_list :: [JSNode] -> Bool
is_irrellevant_list [] = True
is_irrellevant_list (x:xs) = (is_irrellevant_JS x) && (is_irrellevant_list xs)

is_function_call_list :: [JSNode] -> Bool
is_function_call_list (_:(NN (JSArguments _ _ _):_)) = True
is_function_call_list _ = False

is_while :: Node -> Bool
is_while (JSWhile _while _rb _bool _lb _e) = True
is_while _ = False

is_boolresop :: Node -> Bool
is_boolresop (JSExpressionBinary "==" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "===" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "!==" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "!=" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "<" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary ">" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary ">=" _e1 _op _e2) = True
is_boolresop (JSExpressionBinary "<=" _e1 _op _e2) = True
is_boolresop _ = False

is_boolop :: Node -> Bool
is_boolop (JSExpressionBinary "||" _e1 _op _e2) = True
is_boolop (JSExpressionBinary "&&" _e1 _op _e2) = True
is_boolop _ = False

is_intop :: Node -> Bool
is_intop (JSExpressionBinary "+" _e1 _op _e2) = True
is_intop (JSExpressionBinary "-" _e1 _op _e2) = True
is_intop (JSExpressionBinary "*" _e1 _op _e2) = True
is_intop (JSExpressionBinary "/" _e1 _op _e2) = True
is_intop (JSExpressionBinary "%" _e1 _op _e2) = True
is_intop _ = False

is_assign_op :: Node -> Bool
is_assign_op (JSOperator o) = is_equal_JS o
is_assign_op _ = False

is_assign_op_JS :: JSNode -> Bool
is_assign_op_JS = check_JSNode is_assign_op

is_assign_list :: [JSNode] -> Bool
is_assign_list (x:_xs) = is_assign_op_JS x

is_equal :: Node -> Bool
is_equal (JSLiteral "=") = True
is_equal _ = False

is_equal_JS :: JSNode -> Bool
is_equal_JS = check_JSNode is_equal

is_new :: Node -> Bool
is_new (JSLiteral "new") = True
is_new _ = False

is_new_JS :: JSNode -> Bool
is_new_JS = check_JSNode is_new

is_VarDecl :: Node -> Bool 
is_VarDecl (JSVarDecl _x _decl) = True
is_VarDecl _ = False

is_VarDecl_JS :: JSNode -> Bool
is_VarDecl_JS = check_JSNode is_VarDecl

is_funDecl :: Node -> Bool
is_funDecl (JSFunction _function _f _lb _args _rb _e) = True
is_funDecl (JSFunctionExpression _function _ _lb _args _rb _e) = True
is_funDecl _ = False

is_funDecl_JS :: JSNode -> Bool
is_funDecl_JS = check_JSNode is_funDecl

is_objDecl :: Node -> Bool
is_objDecl (JSObjectLiteral _lb _fields _rb) = True
is_objDecl _ = False

is_objDecl_JS :: JSNode -> Bool
is_objDecl_JS = check_JSNode is_objDecl

is_if :: Node -> Bool
is_if (JSIf _if _lb _bool _rb _true _cont) = True
is_if _ = False

is_if_JS :: JSNode -> Bool
is_if_JS = check_JSNode is_if

is_var_acc :: Node -> Bool
is_var_acc (JSIdentifier _x) = True
is_var_acc (JSLiteral "this") = True
is_var_acc _ = False

is_var_acc_JS :: JSNode -> Bool
is_var_acc_JS = check_JSNode is_var_acc

is_field_of_var :: Node -> Bool
is_field_of_var (JSMemberDot [o] _p _field) = is_var_acc_JS o
is_field_of_var (JSMemberSquare [o] _bl _field _br) = is_var_acc_JS o
is_field_of_var _ = False

is_field_of_var_JS :: JSNode -> Bool
is_field_of_var_JS = check_JSNode is_field_of_var

--is_funX :: Node -> Bool
--is_funX (JSExpression [_e1,e2]) = is_arg_JS e2

is_arg_JS :: JSNode -> Bool
is_arg_JS (NN n) = is_arg n
is_arg_JS (NT n _ _) = is_arg_JS (NN n)

is_arg :: Node -> Bool
is_arg (JSArguments _lb _e _rb) = True
is_arg _other = False

is_semicolon_list :: [JSNode] -> Bool
is_semicolon_list [j] = is_semicolon_JS j
is_semicolon_list _other = False

is_int :: Node -> Bool
is_int (JSDecimal _i) = True
is_int _other = False

is_string :: Node -> Bool
is_string (JSStringLiteral _delim _s ) = True
is_string _other = False

is_semicolon_JS :: JSNode -> Bool
is_semicolon_JS = check_JSNode is_semicolon

is_semicolon :: Node -> Bool
is_semicolon (JSLiteral ";") = True
is_semicolon _other = False

-- is the Node list a method call
is_method_call :: [JSNode] -> Bool
is_method_call (jn1:(jn2:_)) = is_obj_acc_JS jn1 && is_argument_JS jn2
                    
is_argument_JS :: JSNode -> Bool
is_argument_JS = check_JSNode is_argument

-- is the Node an object access
is_obj_acc :: Node -> Bool
is_obj_acc (JSMemberDot _ _ _) = True
is_obj_acc (JSMemberSquare _ _ _ _) = True
is_obj_acc _ = False

is_obj_acc_JS :: JSNode -> Bool
is_obj_acc_JS = check_JSNode is_obj_acc

-- is the node an arguments node
is_argument :: Node -> Bool
is_argument (JSArguments _ _ _) = True
is_argument _ = False

-- is the node sequence a call to cordova.exec?
is_cordova_exec_call :: [JSNode] -> Bool
is_cordova_exec_call (js1:(js2:_)) = is_cordova_exec_acc_JS js1 && is_argument_JS js2
is_cordova_exec_call _ = False

--is the node sequence a call to a navigator method?
is_navigator_call :: [JSNode] -> Bool
is_navigator_call (js1:(js2:_)) = is_navigator_acc_JS js1 && is_argument_JS js2
is_navigator_call _ = False

-- is the node sequence an access to cordova.exec
is_cordova_exec_acc_JS :: JSNode -> Bool
is_cordova_exec_acc_JS (NN n) = is_cordova_exec_acc n
is_cordova_exec_acc_JS (NT n _ _) = is_cordova_exec_acc n

is_cordova_exec_acc :: Node -> Bool
is_cordova_exec_acc (JSMemberDot obj _ field) = is_cordova_list obj && is_exec_JS field
is_cordova_exec_acc (JSMemberSquare obj _ field _) = is_cordova_list obj && is_exec_JS field
is_cordova_exec_acc _ = False

-- is the node sequence an access to navigator
is_navigator_acc_list :: [JSNode] -> Bool
is_navigator_acc_list [x] = is_navigator_acc_JS x
is_navigator_acc_list (_:xs) = is_navigator_acc_list xs
is_navigator_acc_list _ = False

is_navigator_acc_JS :: JSNode -> Bool
is_navigator_acc_JS (NN n) = is_navigator_acc n
is_navigator_acc_JS (NT n _ _) = is_navigator_acc n

is_navigator_acc :: Node -> Bool
is_navigator_acc (JSMemberDot objs _sep _field) = is_navigator_acc_list objs
is_navigator_acc (JSMemberSquare objs _lb _field _rb) = is_navigator_acc_list objs
is_navigator_acc (JSIdentifier s) = s == "navigator"
is_navigator_acc _ = False

-- is the node access to the exec identifier
is_exec_JS :: JSNode -> Bool
is_exec_JS (NT n _ _) = is_exec n
is_exec_JS (NN n) = is_exec n

is_exec :: Node -> Bool
is_exec (JSIdentifier s) = s == "exec"
is_exec (JSExpression ss) = is_exec_list ss

is_exec_list :: [JSNode] -> Bool
is_exec_list [] = False
is_exec_list (x:_) = is_exec_JS x

-- is the node sequence access the cordova object
is_cordova_list :: [JSNode] -> Bool
is_cordova_list = is_list_single is_cordova

is_cordova :: Node -> Bool
is_cordova (JSIdentifier s) = s == "cordova"
is_cordova _ = False

-- is the node sequence access the navigator object
is_navigator_list :: [JSNode] -> Bool
is_navigator_list = is_list_single is_navigator 

is_navigator :: Node -> Bool
is_navigator (JSIdentifier s) = s == "navigator"
is_navigator _n = False

-- Auxiliary functions

is_list_single :: (Node -> Bool) -> [JSNode] -> Bool
is_list_single f l | is_single_JSNode l = let
  n = get_single_JSNode l
  in f n
                   | otherwise = False

get_single_JSNode :: [JSNode] -> Node
get_single_JSNode [NN n] = n
get_single_JSNode [NT n _p _cs] = n

is_single_JSNode:: [JSNode] -> Bool
is_single_JSNode [_js] = True
is_single_JSNode _jss = False

int_op :: String -> Bool
int_op "*" = True
int_op "+" = True
int_op "-" = True
int_op "/" = True
--int_op "||" = True
int_op _ = False

or_op :: String -> Bool
or_op "||" = True
or_op "&&" = True
or_op _ = False
