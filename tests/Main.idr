module Main

import System
import System.Directory
import System.File

import Test.Golden

%default covering

------------------------------------------------------------------------
-- Test cases

ttTests : TestPool
ttTests = MkTestPool "TT" [] Nothing
     [ "basic001", "basic002", "basic003",
       "linear001", "linear002", "linear003",
       "relevance001", "relevance002" ]

main : IO ()
main
    = runner $ [ testPaths "tt" ttTests ]
  where
    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
