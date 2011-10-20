-- --------------------------------------------------------------------------
-- Benchmark (Finite Domain)            INRIA Rocquencourt - ChLoE Project --
--                                                                         --
-- Name           : alpha.pl                                               --
-- Title          : alphacipher                                            --
-- Original Source: Daniel Diaz - INRIA France                             --
-- Date           : January 1993                                           --
-- Adapted for MCP: Tom Schrijvers                                                        --
--                                                                         --
-- This problem comes from the news group rec.puzzle.                      --
-- The numbers 1 - 26 have been randomly assigned to the letters of the    --
-- alphabet. The numbers beside each word are the total of the values      --
-- assigned to the letters in the word. e.g for LYRE L,Y,R,E might equal   --
-- 5,9,20 and 13 respectively or any other combination that add up to 47.  --
-- Find the value of each letter under the equations:                      --
--                                                                         --
--    BALLET  45     GLEE  66     POLKA      59     SONG     61            --
--    CELLO   43     JAZZ  58     QUARTET    50     SOPRANO  82            --
--    CONCERT 74     LYRE  47     SAXOPHONE 134     THEME    72            --
--    FLUTE   30     OBOE  53     SCALE      51     VIOLIN  100            --
--    FUGUE   50     OPERA 65     SOLO       37     WALTZ    34            --
--                                                                         --
-- Solution:                                                               --
--  [A, B,C, D, E,F, G, H, I, J, K,L,M, N, O, P,Q, R, S,T,U, V,W, X, Y, Z] --
--  [5,13,9,16,20,4,24,21,25,17,23,2,8,12,10,19,7,11,15,3,1,26,6,22,14,18] --
-- --------------------------------------------------------------------------

import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_void model

model :: FDSolver solver => Tree (FDWrapper solver) [FDExpr solver]
model =
  exist 26 $ 
    \list@[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z] ->
       allin list (1,26) /\
       allDiff list /\
       b + a + l + l + e + t             @=  45 /\
       c + e + l + l + o                 @=  43 /\
       c + o + n + c + e + r + t         @=  74 /\
       f + l + u + t + e                 @=  30 /\
       f + u + g + u + e                 @=  50 /\
       g + l + e + e                     @=  66 /\
       j + a + z + z                     @=  58 /\
       l + y + r + e                     @=  47 /\
       o + b + o + e                     @=  53 /\
       o + p + e + r + a                 @=  65 /\
       p + o + l + k + a                 @=  59 /\
       q + u + a + r + t + e + t         @=  50 /\
       s + a + x + o + p + h + o + n + e @= 134 /\
       s + c + a + l + e                 @=  51 /\
       s + o + l + o                     @=  37 /\
       s + o + n + g                     @=  61 /\
       s + o + p + r + a + n + o         @=  82 /\
       t + h + e + m + e                 @=  72 /\
       v + i + o + l + i + n             @= 100 /\
       w + a + l + t + z                 @=  34 /\
       return list
