module Main

import Test.Golden

%default covering

tests : TestPool
tests = MkTestPool "Frex tests" [] Nothing
  [ "monoids"
  , "commutative-monoids"
  ]

main : IO ()
main = runner [ record { testCases $= map ("frextests/" ++) } tests ]
