import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_void model

model :: FDSolver solver => Tree (FDWrapper solver) [FDExpr solver]
model = 
  exist 5 $ \ns@[n1,n2,n3,n4,n5] -> 
  exist 5 $ \cs@[c1,c2,c3,c4,c5] -> 
  exist 5 $ \ps@[p1,p2,p3,p4,p5] -> 
  exist 5 $ \as@[a1,a2,a3,a4,a5] -> 
  exist 5 $ \ds@[d1,d2,d3,d4,d5] -> 
    let vars = ns ++ cs ++ ps ++ as ++ ds in
    vars `allin` (1,5) /\
    allDiff ns /\
    allDiff cs /\
    allDiff ps /\
    allDiff as /\
    allDiff ds /\
    n1 @= c2   /\
    n2 @= a1   /\
    n3 @= p1   /\
    n4 @= d3   /\
    n5 @= 1    /\
    d5 @= 3    /\
    p3 @= d1   /\
    c1 @= d4   /\
    p5 @= a4   /\
    p2 @= c3   /\
    c1 @= c5+1 /\
    plusorminus a3 p4 1 /\
    plusorminus a5 p2 1 /\
    plusorminus n5 c4 1 /\
    return vars 

plusorminus x y c =
  x @= y+c \/ x @= y-c
