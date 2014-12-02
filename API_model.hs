module API_model where

import JST0P_context
import JST0P_types
import JST0_type_aux

init_context :: ContextAn
init_context = let
  (ps,ts) = apis
  g = JST0P_context.empty_empty
  in var_set_path_list g ps ts

apis :: ([Path],[(TypeAn,FieldType)])
apis = lp2pl api_pairs

api_pairs :: [(Path,TypeP)]
api_pairs = [
  (["navigator","geolocation","getLocation"],JST0P_Function objectP_empty [JST0P_Int] (I 1) JST0P_Int (I 0) )
            ]

lp2pl :: [(Path,TypeP)] -> ([Path],[(TypeAn,FieldType)])
lp2pl [] = ([],[])
lp2pl (p:ps) = let
  (ss,ts) = lp2pl ps
  (s,t) = p
  in (s:ss,((t,I 0),Definite):ts)

