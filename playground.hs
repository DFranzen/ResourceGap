import Language.JavaScript.Parser.Parser

import Data.Map as Map

parser :: String -> IO()
parser s = do
  putStr (show (parse s "test.js"))

main ::IO()
main = putStr "blubb"
