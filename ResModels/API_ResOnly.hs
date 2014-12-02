module API_model where

import JST0_context
import JST0_types
import JST0_type_aux

init_context :: Context
init_context = JST0_context.empty

apis :: ([Path],[Type])
apis = lp2pl api_pairs

api_pairs :: [(Path,Type)]
api_pairs = []

lp2pl :: [(Path,Type)] -> ([Path],[Type])
lp2pl [] = ([],[])
lp2pl (p:ps) = let
  (ss,ts) = lp2pl ps
  (s,t) = p
  in (s:ss,t:ts)

