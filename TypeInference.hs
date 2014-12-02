module TapeInference where

import Language.JavaScript.Parser.Parser
import Language.JavaScript.Parser.AST

import JST0_constrain
import JST0_type_aux
import JST0_solution
import JST0P_context
import JST0P_solution
import JST0P_types
import JST0P_constrain

import API_model
import ConstGen
import Closure
import AnnotGen

import Control.Monad.LPMonad
import Data.LinearProgram

import Data.Map as Map
--import Maps

import Debugging

main :: IO()
main = do
  fname <- getLine
  ti_file fname

fp_string :: String -> IO()
fp_string s = let
  p = parse s "test.js"
  in fp_EAST p

ti_string :: String -> IO()
ti_string s = let
  p = parse s "test.js"
  in ti_EAST p

--first pass for an Either AST or ErrorString
fp_EAST :: Either String JSNode -> IO()
fp_EAST p = case p of
  (Left e) -> putStr ("Parsing Error: " ++ e)
  Right j -> let
    g_init = deg_context init_context
    (_a,gamma) = fp_JSNode (0,g_init) j
    in putStr ("Variables: " ++ (show (Map.keys gamma)))

       
-- type inference for an Either AST or ErrorString
ti_EAST :: Either String JSNode -> IO()
ti_EAST p = case p of
    (Left e) -> putStr ("Parsing Error: " ++ e)
    Right j -> let
      -- initialise Context with API types
      g_init | trace 5 ("computing API model") True = init_context
             | True = undefined
      gminus_init | trace 5 ("reducing API model") True = deg_context g_init
                  |True = undefined
      (a0,gamma0) |trace 5 ("executing first pass") True= fp_JSNode (0,gminus_init) j
      -- infer Constraints
      (a,t,_gamma,c) |trace 5 ("constraint generation") True = cg_JSNode (a0,gamma0) j
      -- Close type constraints
      c_c | trace 5 ("closing constraints") True = close_constraints c
          | True = undefined
      hl = extract_HL_types c_c
      csinfo = cs_show_varinfo c
      -- Extract solution
      sol = extract_solution c_c
      well_defined = JST0_solution.check_solution sol c
      (solP,bstartp) | well_defined = solutionP_from_solution sol
      g_initSol = sol_set g_init solP
      (ap0,bstart,gammap0,nvar) = fpp_JSNode (0,bstartp,solP,g_initSol) j
      --(gammap0,bstart) = aug_context gamma0 bstartp solP
      (_af,bf,tf,nf,gf,cfp) = ag_JSNode (ap0,bstart+2,gammap0,N (bstart+1),solP) j
      cf = concat[cfp,[Gt [N bstart] [N (bstart+1),I nvar]]]
      in do
        -- JST0 information
        output ("----------------------------------------\n-- Types\n----------------------------------------\n")
        output ("Direct Constraints: " ++ (show c) ++ "\n")
        output ("Closed Constraints: " ++ (show c_c) ++ "\n")
        output ("Higher Level Types: " ++ (show hl) ++ "\n")
        output ("Solution: " ++ (show sol) ++ "\n")
        output ("Used Variables: " ++ (show a) ++ "\n")
        output ("TV Info: " ++ csinfo ++ "\n")
        output ("Type: " ++ show t ++ "\n")
        output ("----------------------------------------\n-- Annotations\n----------------------------------------\n")
        (_,Just (_,annsol)) <- glpSolveVars mipDefaults (lp (bf) cf)
        output ("Initial Context: " ++ (show gammap0) ++ "\n")
        output ("Constraints: " ++ (show cf) ++ "\n")
        output ("Used Variables: " ++ (show bf) ++ "\n")
        output ("Solution: " ++  show_solutionP solP ++ "\n")
        output ("Annotation Solution: " ++ (show annsol) ++ "\n")
        output ("----------------------------------------\n-- Results\n----------------------------------------\n")
        output ("Variable Types [before execution]: \n" ++ (get_full_variable_types (var_names gammap0) gammap0 annsol) ++ "\n\n")
        output ("Variable Types [after execution]: \n" ++ (get_full_variable_types (var_names gf) gf annsol) ++ "\n\n")
        output ("whole program: (N " ++ show bstart ++ ") -> " ++ (show tf) ++ ", " ++ show nf ++ "\n")
        output ("whole program: " ++ (show (Map.lookup ("n_" ++ show bstart) annsol)) ++ "->" ++ (printSol_P tf annsol) ++ "," ++ (show (Map.lookup (show nf) annsol)) ++"\n\n")
  
ti_file :: String -> IO()
ti_file fname = do
                s <- readFile fname
                ti_string s

output :: String -> IO()
output s = putStr s
--output _ = return()

----------------------------------------
-- Construct LPPs
----------------------------------------

lp :: Int-> [ConstrainAn] -> LP String Int
lp a cs = execLPM $ do   setDirection Min
                         setObjective (objFun a)
                         get_lp cs
--                         geqTo (linCombination[(1,"n_0"),((-1),"n_2"),((-1),"n_1")]) 1
--                         geqTo (linCombination[(1,"n_2")]) 0
                         set_varKind a
                         set_pos a

get_lp :: [ConstrainAn] -> LPM String Int ()
get_lp [] = geqTo Map.empty 0
get_lp [x] = get_lp_one x
get_lp (x:xs) = do (get_lp_one x)
                   get_lp xs


-- Generates a lpp from one constraint.
get_lp_one :: ConstrainAn -> LPM String Int ()
get_lp_one (Gt a b) = let (lpos,ipos) = get_linCom   1  a
                          (lneg,ineg) = get_linCom (-1) b
                      in geqTo (linCombination (concat [lpos,lneg])) (-ineg-ipos)

-- convert a list of Annotations into a linear combination with the factor a for each of the summands.
-- Arguments:
--  - Factor for each of the summands
--  - List of annotations to sum up in the lin comb
-- Returns:
--  - Linear Combination of all variables
--  - Sum of all integers in the original list
get_linCom :: Int -> [Annotation] -> ([(Int,String)],Int)
get_linCom _ [] = ([],0)
get_linCom a ((N n):xs) = let
  (l,i) = get_linCom a xs
  in ((a,show (N n)):l,i)
get_linCom a ((I n):xs) = let
  (l,i) = get_linCom a xs
  in (l,i+(a*n))

set_pos :: Int -> LPM String Int ()
set_pos 0 = do varGeq "n_0" 0
set_pos a = do varGeq ("n_" ++ (show a)) 0
               set_pos (a-1)

set_varKind :: Int -> LPM String Int ()
set_varKind 0 = do setVarKind "n_0" IntVar
set_varKind a = do
  set_varKind (a-1)
  setVarKind ("n_" ++ (show a)) IntVar

objFun :: Int -> LinFunc String Int
objFun a = linCombination (objFun_list a)

objFun_list :: Int -> [(Int,String)]
objFun_list 0 = []
objFun_list a = let
  prv = objFun_list (a-1)
  in (1,"n_" ++ show a):prv

obj_3 :: LinFunc String Int
obj_3 = linCombination [(1,"n_0"),(1,"n_1"),(1,"n_2")]

get_full_variable_types :: [String] -> ContextAn -> Map String Double -> String
get_full_variable_types ss e m = Prelude.foldl (\a b -> (a ++ "\n" ++ b ++ ":" ++ get_full_variable_type b e m)) "" ss

get_full_variable_type :: String -> ContextAn -> Map String Double -> String
get_full_variable_type s e m = let (t,psi) = var_get e s
                               in printSol_member s (t,psi) m

printSol_P :: TypeP -> Map String Double -> String
printSol_P (JST0P_Object a mem) sol = "µ" ++ (show a) ++ ".(" ++ (printSol_members mem sol) ++ ")"
printSol_P (JST0P_Function t1 t2 n1 t3 n2) sol = "<" ++ (printSol_P t1 sol) ++ "⨯" ++ (printSol_list t2 sol) ++ "," ++ (printSol_Ann n1 sol) ++ "->" ++ (printSol_P t3 sol) ++ "," ++ (printSol_Ann n2 sol) ++ ">"
printSol_P t _sol = show t

printSol_list :: [TypeP] -> Map String Double -> String
printSol_list xs m = "(" ++ (printSol_P_list xs m) ++ ")"

printSol_P_list :: [TypeP] -> Map String Double -> String
printSol_P_list [] _m = ""
printSol_P_list [x] m = printSol_P x m
printSol_P_list (x:xs) m = (printSol_P x m) ++ "," ++ (printSol_P_list xs m)

printSol_Ann :: Annotation -> Map String Double -> String
printSol_Ann (N a) sol = let i = Map.lookup ("n_" ++ (show a)) sol
                         in case i of
                           Just k -> show k
                           Nothing -> "Variable " ++ show i ++ "not found"
printSol_Ann a _sol = show a

printSol_members :: MembersAn -> Map String Double -> String
printSol_members mem sol = "{" ++ (Map.foldWithKey (\s ty prv -> prv ++ (printSol_member s ty sol)) "" mem) ++ "}"

printSol_member :: String -> (TypeAn,FieldType) -> Map String Double -> String
printSol_member s (t,tf) sol = (show s) ++ ":" ++ (printSol_An t sol) ++ (show tf) ++ ","

printSol_An :: TypeAn -> Map String Double -> String
printSol_An (t,n) sol = "(" ++ printSol_P t sol ++ "," ++ (printSol_Ann n sol) ++ ")"
