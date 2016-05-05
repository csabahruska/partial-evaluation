module ReduceTest where

import Reduce

powerFun =
  ELet C "power" (ELam C "x" $ ELam C "n" $ EBody C $ ifZero (EVar C "n")
    (ELit C $ LFloat 1.0)
    (EApp C (EApp C (EPrimFun C PMul) (EVar C "x"))
            (EApp C (EApp C (EVar C "power") (EVar C "x")) (EApp C (EApp C (EPrimFun C PAdd) (ELit C $ LFloat $ -1.0)) (EVar C "n"))))
  )

reduceExp = powerFun $ EApp C (EApp C (EVar C "power") (ELit C $ LFloat 2.0)) (ELit C $ LFloat 4.0)

lit0R = ELit R $ LFloat 0.0
lit1R = ELit R $ LFloat 1.0
lit10R = ELit R $ LFloat 10.0

lit0 = ELit C $ LFloat 0.0
lit1 = ELit C $ LFloat 1.0
lit2 = ELit C $ LFloat 2.0
lit3 = ELit C $ LFloat 3.0

ifZero v t e = EApp C (EApp C (EApp C (EPrimFun C PIfZero) v) t) e

idFun = ELet C "id" (ELam C "x" $ EVar C "x")
reduceId = idFun $ EApp C (EVar C "id") lit1

lamIdFun = ELam C "x" $ EVar C "x"
reduceLamId = EApp C lamIdFun lit1

lamFun = ELam C "x" $ ELam C "y" $ EVar C "x"
reduceLamFun = EApp C (EApp C lamFun lit1) lit2

lamMixFun1 = ELam C "x" $ ELam R "y" $ ELam C "z" $ EApp R (EVar C "x") (EVar C "z") -- let fun = \x@C -> \y@R -> \z@C -> x@C z@C
reduceLamMix1 = EApp C (EApp R (EApp C lamMixFun1 lit1) (EVar R "a")) lit2 -- fun 1.0@C a@R 2.0@C ==> (\y -> 1.0 2.0) a

let0 = ELet C "v" lit1 $ EVar C "v"
let1 = ELet R "v" lit1 $ EVar R "v"

add = EApp C (EApp C (EPrimFun C PAdd) lit1) lit2
mul = EApp C (EApp C (EPrimFun C PMul) lit1) lit2

letFun0 = ELet C "v" (ELam C "x" $ EBody C $ EVar C "x") $ EApp C (EVar C "v") lit1
letFun1 = ELet C "f" (ELam C "x" $ ELam C "y" $ EBody C $ ifZero (EVar C "x") (EVar C "y") (EApp C (EApp C (EVar C "f") (EVar C "y")) (EVar C "x"))) $
  EApp C (EApp C (EVar C "f") lit2) lit0

reduceIfZero = ifZero lit0 lit1 lit2

primMulC x y = EApp C (EApp C (EPrimFun C PMul) x) y
-------- specialization test
primAddR x y = EApp R (EApp R (EPrimFun R PAdd) x) y
specFun0 = ELam R "x" $ ELam C "y" $ EBody R $ primAddR (EVar R "x") (EVar C "y")
letSpecFun0 = ELet C "f" specFun0 $ EApp C (EApp R (EVar C "f") lit1R) lit2
letSpecFun1 = ELet C "f" specFun0 $ EApp C (EApp R (EVar C "f") (EApp C (EApp R (EVar C "f") lit1R) lit2)) lit3


specFun2 = ELam R "x" $ ELam C "y" $ ELam R "z" $ EBody R $ primAddR (EVar R "x") (EVar C "y")
letSpecFun2 = ELet C "f" specFun2 $ EApp R (EApp C (EApp R (EVar C "f") lit1R) lit2) lit10R


specFun3 = ELam R "x" $ ELam C "y" $ ELam R "z" $ EBody R $ primMulC lit2 lit3
partEval1 = ELet C "f" specFun3 $ lit0
{-
  the generic function "f" should not be used in the residual; should be replaced with the specialised functions in the same scope
-}

powerFunR =
  ELet C "power" (ELam R "x" $ ELam C "n" $ EBody R $ ifZero (EVar C "n")
    (ELit C $ LFloat 1.0)
    (EApp R (EApp R (EPrimFun R PMul) (EVar R "x"))
            (EApp C (EApp R (EVar C "power") (EVar R "x")) (EApp C (EApp C (EPrimFun C PAdd) (ELit C $ LFloat $ -1.0)) (EVar C "n"))))
  )

powerFunR' =
  ELet C "power" (ELam C "n" $ ELam R "x" $ EBody R $ ifZero (EVar C "n")
    (ELit C $ LFloat 1.0)
    (EApp R (EApp R (EPrimFun R PMul) (EVar R "x"))
            (EApp R (EApp C (EVar C "power") (EApp C (EApp C (EPrimFun C PAdd) (ELit C $ LFloat $ -1.0)) (EVar C "n"))) (EVar R "x")))
  )

powerExpR = powerFunR $ EApp C (EApp R (EVar C "power") lit2) lit1
powerExpR' = powerFunR' $ EApp R (EApp C (EVar C "power") lit1) lit2
powerExpR1 = powerFunR $ EApp C (EApp R (EVar C "power") lit2) lit2

-------- pattern match test
case0 = ELet C "x" (ECon C "Just" [lit2]) $ ECase C (EVar C "x") [Pat "Just" ["a"] (EVar C "a")]
case1 = ELet R "x" (ECon R "Just" [lit2]) $ ECase R (EVar R "x") [Pat "Just" ["a"] (EVar R "a")]
resultCase0 = ELit C (LFloat 2.0)
resultCase1 = ELet R "x" (ECon R "Just" [ELit C (LFloat 2.0)]) (ECase R (EVar R "x") [Pat "Just" ["a"] (EVar R "a")])


test = runReduce reduceLamId
test1 = runReduce reduceLamFun
test2 = runReduce reduceLamMix1
test3 = runReduce let0
test4 = runReduce let1
test5 = runReduce add
test6 = runReduce mul
test7 = runReduce letFun0
test8 = runReduce reduceIfZero
test9 = runReduce letFun1
test10 = runReduce letSpecFun0
test11 = runReduce letSpecFun1
test12 = runReduce powerExpR
test13 = runReduce powerExpR1

testPower = runReduce reduceExp

result = ELit C (LFloat 1.0)
result1 = ELit C (LFloat 1.0)
result2 = EApp R (ELam R "y" (EApp R (ELit C (LFloat 1.0)) (ELit C (LFloat 2.0)))) (EVar R "a")
result3 = ELit C (LFloat 1.0)
result4 = ELet R "v" (ELit C (LFloat 1.0)) (EVar R "v")
result5 = ELit C (LFloat 3.0)
result6 = ELit C (LFloat 2.0)
result7 = ELit C (LFloat 1.0)
result8 = ELit C (LFloat 1.0)
result9 = ELit C (LFloat 2.0)
resultPower = ELit C (LFloat 16.0)
result10 = ELet R "f0" (ELam R "x" (EBody R (EApp R (EApp R (EPrimFun R PAdd) (EVar R "x")) (ELit C (LFloat 2.0))))) (EApp R (EVar R "f0") (ELit R (LFloat 1.0)))
result11 =
   ELet R "f0" (ELam R "x" (EBody R (EApp R (EApp R (EPrimFun R PAdd) (EVar R "x")) (ELit C (LFloat 2.0)))))
  (ELet R "f1" (ELam R "x" (EBody R (EApp R (EApp R (EPrimFun R PAdd) (EVar R "x")) (ELit C (LFloat 3.0)))))
  (EApp R (EVar R "f1") (EApp R (EVar R "f0") (ELit R (LFloat 1.0)))))

result12 =
   ELet R "power0" (ELam R "x" (EBody R (ELit C (LFloat 1.0))))
  (ELet R "power1" (ELam R "x" (EBody R (EApp R (EApp R (EPrimFun R PMul) (EVar R "x")) (EApp R (EVar R "power0") (EVar R "x")))))
  (EApp R (EVar R "power1") (ELit C (LFloat 2.0))))

result13 =
   ELet R "f0" (ELam R "x" (ELam R "z" (EBody R (EApp R (EApp R (EPrimFun R PAdd) (EVar R "x")) (ELit C (LFloat 2.0))))))
  (EApp R (EApp R (EVar R "f0") (ELit R (LFloat 1.0))) (ELit R (LFloat 10.0)))

tests =
  [ (test,result)
  , (test1,result1)
--  , (test2,result2)
  , (test3,result3)
  , (test4,result4)
  , (test5,result5)
  , (test6,result6)
  , (test7,result7)
  , (test8,result8)
  , (test9,result9)
  , (testPower,resultPower)
  , (test10,result10)
  , (test11,result11)
  , (test12,result12)
  , (runReduce powerExpR',result12)
  , (runReduce case0,resultCase0)
  , (runReduce case1,resultCase1)
  , (runReduce letSpecFun2, result13)
  ]

ok = mapM_ (\(a,b) -> putStrLn $ show (a == b) ++ " - " ++ show b) tests

higherTest =
       ELet C "map" (ELam C "f" (ELam C "x" (EBody C
                (ECase C (EVar C "x")
                  [Pat "Nil" [] (ECon C "Nil" [])
                  ,Pat "Cons" ["a","xs"] (ECon C "Cons" [EApp C (EVar C "f") (EVar C "a"),EApp C (EApp C (EVar C "map") (EVar C "f")) (EVar C "xs")])
                  ]))))
      (ELet C "l" (EBody C (ECon C "Cons" [ELit C (LFloat 1.0),ECon C "Cons" [ELit C (LFloat 2.0),ECon C "Cons" [ELit C (LFloat 3.0),ECon C "Nil" []]]]))
      (ELet C "go" (ELam C "z" (EBody C
                (ECase C (EVar C "z")
                  [Pat "Nil" [] (ELit C (LFloat 0.0))
                  ,Pat "Cons" ["b","bs"] (EApp C (EApp C (EPrimFun C PAdd) (EVar C "b")) (EApp C (EVar C "go") (EVar C "bs")))])))
      (ELet C "five" (ELam C "y" (EBody C
                (EApp C (EApp C (EPrimFun C PMul) (ELit C (LFloat 5.0))) (EVar C "y"))))

      (EApp C (EVar C "go") (EApp C (EApp C (EVar C "map") (EVar C "five")) (EVar C "l"))))))

mapTest =
  ELet C "map" (ELam C "f" (ELam C "x" (EBody C
            (ECase C (EVar C "x")
              [Pat "Nil" [] (ECon C "Nil" [])
              ,Pat "Cons" ["a","xs"] (ECon C "Cons" [EApp C (EVar C "f") (EVar C "a"),EApp C (EApp C (EVar C "map") (EVar C "f")) (EVar C "xs")])
              ]))))
  (ELet C "five" (ELam C "y" (EBody C
            (EApp C (EApp C (EPrimFun C PMul) (ELit C (LFloat 5.0))) (EVar C "y"))))

  (EApp C (EApp C (EVar C "map") (EVar C "five")) (ECon C "Cons" [ELit C (LFloat 3.0),ECon C "Nil" []])))
