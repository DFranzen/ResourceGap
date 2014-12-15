import Language.JavaScript.Parser.Parser

import Data.Map as Map
import Data.Set as Set

parser :: String -> IO()
parser s = do
  putStr (show (parse s "test.js"))

main ::IO()
main = putStr "blubb"

testset :: Set Int
testset = let
  l2 = Set.fromList [1,2,3]
  l3 = Set.fromList [3,4,5,6,7]
  in Set.difference l2 l3
