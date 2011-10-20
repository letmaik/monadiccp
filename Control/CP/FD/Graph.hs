{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/MCP/
 - 	Pieter Wuille
 -}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.CP.FD.Graph (
  EGConstraintSpec(..),
  EGParTerm(..),
  EGParBoolTerm(..),
  EGParColTerm(..),
  EGPar, EGBoolPar, EGColPar,
  EGConsArgs,
  EGEdgeId,
  EGVarId(..),
  EGVarType(..),
  EGTypeData(..),
  EGEdge(..),
  EGModel(..),
  addEdge,
  addNode,
  delNode,
  findEdge,
  unifyNodes,
  unifyIds,
  baseGraph,
  baseTypeData,
  egTypeDataMap, egTypeGet, egTypeMod,
  present,
  getConnectedEdges,
  externMap, filterModel, emptyModel, pruneNodes,
) where

import Control.Monad (foldM)

import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as Map

import Data.Expr.Data
-- import Control.CP.FD.Expr.Util

-- BoolEqual, Rel _ (EREqual) _, ColEqual are encoded in the graph itself, and
-- not represented as constraints between them

data EGVarType = 
    EGBoolType
  | EGIntType
  | EGColType
  deriving (Eq,Show)

-- instance KeyableExpr EGConstraintSpec where
--  keyCompare a b = compare a b

data EGConstraintSpec =
    EGIntValue EGPar                 -- i0 == p
  | EGBoolValue EGBoolPar            -- b0 == p
  | EGColValue EGColPar              -- c0 == p
  | EGIntExtern Int                  -- super[p] == i0
  | EGBoolExtern Int                 -- super[p] == b0
  | EGColExtern Int                  -- super[p] == c0
  | EGPlus                           -- i0==i1+i2
  | EGMinus                          -- i0==i1-i2
  | EGMult                           -- i0==i1*i2
  | EGDiv                            -- i0==i1/i2   {- (i0==i1/i2) is NOT the same as (i1==i0*i2) -}
  | EGMod                            -- i0==i1%i2  
  | EGAbs                            -- i0==abs(i1)
  | EGAt                             -- i0==c0[i1]
  | EGFold EGModel (Int,Int,Int)     -- i0==fold(p,i1,c0)  {- inner intExtern(-1) is fold-function's return value, intExtern(-2) is the accumulator, intExtern(-3) is the argument -}
  | EGSize                           -- i0==size(c0)
  | EGChannel                        -- int(b0) == i0
  | EGList Int                       -- c0 == [i0,i1,i2,...] (len p) 
  | EGRange                          -- c0 == [i0..i1]
  | EGMap EGModel (Int,Int,Int)      -- c0 == map(p,c1)    {- inner intExtern(-1) is map-function's return value, intExtern(-2) is its argument -}
  | EGSlice EGModel (Int,Int,Int)    -- c0 == c1[f(0)...f(i0-1)]; inner model defines f: intExtern(-1) is return value, intExtern(-2) is its argument
--  | EGSlice (EGPar -> EGPar) EGPar   -- c0 == c1[f(0)...f(n-1)]
  | EGCat                            -- c0 == c1++c2
  | EGAnd                            -- b0 == b1 && b2
  | EGOr                             -- b0 == b1 || b2
  | EGEquiv                          -- b0 == (b1 == b2)
  | EGNot                            -- b0 == !b1
  | EGEqual                          -- b0 <-> i0 == i1
  | EGDiff                           -- b0 <-> i0 /= i1
  | EGLess Bool                      -- false: b0 <-> i0 <= i1 ; true: b0 <-> i0 < i1
  | EGAll EGModel (Int,Int,Int) Bool -- b0 <-> foreach (i from c0): p(i)  {- inner boolExtern(-1) is truth value of predicate, intExtern(-1) is its argument; bool is true if all inner predicates need to be true -}
  | EGAny EGModel (Int,Int,Int) Bool -- b0 <-> forany (i from c0): p(i)   {- inner boolExtern(-1) is truth value of predicate, intExtern(-1) is its argument; bool is true if all inner predicates need to be false -}
--  | EGAllC EGModel (Int,Int,Int) Bool -- b0 <-> foreach (i from [i0,i1]: p(i) {- inner boolExtern(-1) is truth value of predicate, intExtern(-1) is its (constant) argument; bool is true if all inner predicates need to be true -}
--  | EGAnyC EGModel (Int,Int,Int) Bool -- b0 <-> foreach (i from [i0,i1]: p(i) {- inner boolExtern(-1) is truth value of predicate, intExtern(-1) is its (constant) argument; bool is true if all inner predicates need to be true -}
  | EGSorted Bool                    -- c0 is increasing (false), or strictly increasing (true)
  | EGAllDiff Bool                   -- c0 is all different (b0 means: use in consistency)
  | EGDom                            -- i0 is any of c0
  | EGCondEqual                      -- b0 ? (b1==b2) : true
  | EGCondInt                        -- i0 = b0 ? i1 : i2
  deriving (Eq,Show)

instance Ord (EGPar -> EGPar) where
  compare a b = compare (a (Term (EGPTParam (-1)))) (b (Term (EGPTParam (-1))))

instance Eq (EGPar -> EGPar) where
  a == b = (a (Term (EGPTParam (-1)))) == (b (Term (EGPTParam (-1))))

instance Show (EGPar -> EGPar) where
  show f = show $ f (Term (EGPTParam (-1)))

dummyConstraint :: EGConstraintSpec -> Bool
dummyConstraint c = case c of
  EGIntExtern _ -> True
  EGBoolExtern _ -> True
  EGColExtern _ -> True
  _ -> False

data EGParTerm =
    EGPTParam Int
  deriving (Show,Eq,Ord)
  
data EGParBoolTerm =
    EGPTBoolParam Int
  deriving (Show,Eq,Ord)

data EGParColTerm =
    EGPTColParam Int
  deriving (Show,Eq,Ord)

type EGPar =     Expr     EGParTerm EGParColTerm EGParBoolTerm
type EGBoolPar = BoolExpr EGParTerm EGParColTerm EGParBoolTerm
type EGColPar =  ColExpr  EGParTerm EGParColTerm EGParBoolTerm

-- Bools, Ints, Cols
type EGConsArgs = (Int,Int,Int)

getConsArgs :: EGConstraintSpec -> EGTypeData Int
getConsArgs x = case
  case x of
    EGBoolValue _    -> (1,0,0)
    EGIntValue _     -> (0,1,0)
    EGColValue _     -> (0,0,1)
    EGIntExtern _    -> (0,1,0)
    EGBoolExtern _   -> (1,0,0)
    EGColExtern _    -> (0,0,1)
    EGPlus           -> (0,3,0)
    EGMinus          -> (0,3,0)
    EGMult           -> (0,3,0)
    EGDiv            -> (0,3,0)
    EGMod            -> (0,3,0)
    EGAbs            -> (0,2,0)
    EGAt             -> (0,2,1)
    EGFold _ (a,b,c) -> (a,2+b,1+c)
    EGSize           -> (0,1,1)
    EGChannel        -> (1,1,0)
    EGList n         -> (0,n,1)
    EGRange          -> (0,2,1)
    EGMap _ (a,b,c)  -> (a,b,2+c)
    EGSlice _ (a,b,c) -> (a,1+b,2+c)
    EGCat            -> (0,0,3)
    EGAnd            -> (3,0,0)
    EGOr             -> (3,0,0)
    EGEquiv          -> (3,0,0)
    EGNot            -> (2,0,0)
    EGEqual          -> (1,2,0)
    EGDiff           -> (1,2,0)
    EGLess _         -> (1,2,0)
    EGAll _ (a,b,c) _ -> (1+a,b,1+c)
    EGAny _ (a,b,c) _ -> (1+a,b,1+c)
--    EGAllC _ (a,b,c) _ -> (1+a,2+b,c)
--    EGAnyC _ (a,b,c) _ -> (1+a,2+b,c)
    EGSorted _       -> (0,0,1)
    EGAllDiff _      -> (0,0,1)
    EGDom            -> (0,1,1)
    EGCondEqual      -> (3,0,0)
    EGCondInt        -> (1,3,0)
  of (a,b,c) -> EGTypeData { boolData = a, intData = b, colData =c }

newtype EGEdgeId = EGEdgeId { unEGEdgeId :: Int }
  deriving (Eq,Ord,Show)

data EGVarId = EGVarId { unVarId :: Int }
  deriving (Eq,Ord,Show)

data EGTypeData x = EGTypeData {
  boolData :: x,
  intData :: x,
  colData :: x
}

deriving instance Show x => Show (EGTypeData x)
deriving instance Eq x => Eq (EGTypeData x)

baseTypeData :: x -> EGTypeData x
baseTypeData x = EGTypeData {
  boolData = x,
  intData = x,
  colData = x
}

egTypeDataMap :: ((forall a. EGTypeData a -> a) -> b) -> EGTypeData b
egTypeDataMap f = EGTypeData {
  boolData = f boolData,
  intData = f intData,
  colData = f colData
}

egTypeGet :: EGVarType -> EGTypeData a -> a
egTypeGet EGBoolType = boolData
egTypeGet EGIntType = intData
egTypeGet EGColType = colData

egTypeMod :: EGVarType -> EGTypeData a -> (a -> a) -> EGTypeData a
egTypeMod EGBoolType d f = d { boolData = f $ boolData d }
egTypeMod EGIntType d f = d { intData = f $ intData d }
egTypeMod EGColType d f = d { colData = f $ colData d }

data EGEdge = EGEdge {
  egeCons :: EGConstraintSpec,
  egeLinks :: EGTypeData [EGVarId]
} deriving (Eq,Show)

showBool :: EGVarId -> String
showBool (EGVarId i) = "b" ++ (show i)
showInt :: EGVarId -> String
showInt (EGVarId i) = "i" ++ (show i)
showCol :: EGVarId -> String
showCol (EGVarId i) = "c" ++ (show i)

showLst :: (EGVarId -> String) -> [EGVarId] -> String
showLst _ [] = "[]"
showLst f x = "[" ++ (foldl1 (\x y -> x ++ "," ++ y) $ map f x) ++ "]"

instance Display EGEdge where
  displayer (EGEdge { egeCons = EGBoolValue i, egeLinks = EGTypeData { boolData = [l] } }) = displaySingle $ (showBool l) ++ " == " ++ "#["++(show i)++"]"
  displayer (EGEdge { egeCons = EGIntValue i, egeLinks =  EGTypeData { intData = [l] }}) = displaySingle $ (showInt l) ++ " == " ++ "#["++(show i)++"]"
  displayer (EGEdge { egeCons = EGColValue i, egeLinks =  EGTypeData { colData = [l] }}) = displaySingle $ (showCol l) ++ " == " ++ "#["++(show i)++"]"
  displayer (EGEdge { egeCons = EGBoolExtern i, egeLinks = EGTypeData  { boolData = [l] }}) = displaySingle $ (showBool l) ++ " == parentBool[" ++ (show i) ++ "]"
  displayer (EGEdge { egeCons = EGIntExtern i, egeLinks =  EGTypeData { intData = [l] }}) = displaySingle $ (showInt l) ++ " == parentInt[" ++ (show i) ++ "]"
  displayer (EGEdge { egeCons = EGColExtern i, egeLinks = EGTypeData  { colData = [l] }}) = displaySingle $ (showCol l) ++ " == parentCol[" ++ (show i) ++ "]"
  displayer (EGEdge { egeCons = EGPlus, egeLinks =  EGTypeData { intData=[a,b,c] }}) = displaySingle $ (showInt a) ++ " == " ++ (showInt b) ++ " + " ++ (showInt c)
  displayer (EGEdge { egeCons = EGMinus, egeLinks =  EGTypeData { intData=[a,b,c] }}) = displaySingle $ (showInt a) ++ " == " ++ (showInt b) ++ " - " ++ (showInt c)
  displayer (EGEdge { egeCons = EGMult, egeLinks =  EGTypeData { intData=[a,b,c] }}) = displaySingle $ (showInt a) ++ " == " ++ (showInt b) ++ " * " ++ (showInt c)
  displayer (EGEdge { egeCons = EGDiv, egeLinks =  EGTypeData { intData=[a,b,c] }}) = displaySingle $ (showInt a) ++ " == " ++ (showInt b) ++ " / " ++ (showInt c)
  displayer (EGEdge { egeCons = EGMod, egeLinks =  EGTypeData { intData=[a,b,c] }}) = displaySingle $ (showInt a) ++ " == " ++ (showInt b) ++ " % " ++ (showInt c)
  displayer (EGEdge { egeCons = EGAbs, egeLinks =  EGTypeData { intData=[a,b] }}) = displaySingle $ (showInt a) ++ " == abs(" ++ (showInt b) ++ ")"
  displayer (EGEdge { egeCons = EGAt, egeLinks =  EGTypeData { intData=[a,b], colData=[c] }}) = displaySingle $ (showInt a) ++ " == " ++ (showCol c) ++ "[" ++ (showInt b) ++ "]"
  displayer (EGEdge { egeCons = EGSize, egeLinks =  EGTypeData { intData=[a], colData=[c] }}) = displaySingle $ (showInt a) ++ " == size(" ++ (showCol c) ++ ")"
  displayer (EGEdge { egeCons = EGDom, egeLinks =  EGTypeData { intData=[a], colData=[c] }}) = displaySingle $ ("dom(" ++ (showInt a) ++ ") == " ++ (showCol c))
  displayer (EGEdge { egeCons = EGChannel, egeLinks =  EGTypeData { boolData=[a], intData=[b] }}) = displaySingle $ (showBool a) ++ " == " ++ (showInt b)
  displayer (EGEdge { egeCons = EGList 0, egeLinks =  EGTypeData { colData=[c] }}) = displaySingle $ (showCol c) ++ " == []"
  displayer (EGEdge { egeCons = EGList _, egeLinks =  EGTypeData { intData=l, colData=[c] }}) = displaySingle $ (showCol c) ++ " == ["++(foldl1 (\a b -> a ++","++b) $ map showInt l)++"]"
  displayer (EGEdge { egeCons = EGAllDiff _, egeLinks =  EGTypeData { colData=[c] }}) = displaySingle $ "allDiff " ++ (showCol c)
  displayer (EGEdge { egeCons = EGSorted b, egeLinks =  EGTypeData { colData=[c] }}) = displaySingle $ "sorted " ++ (show b) ++ " " ++ (showCol c)
  displayer (EGEdge { egeCons = EGRange, egeLinks =  EGTypeData { intData=[l,h], colData=[c] }}) = displaySingle $ (showCol c) ++ " == ["++(showInt l)++".."++(showInt h)++"]"
--  displayer (EGEdge { egeCons = EGSlice f n, egeLinks =  EGTypeData { colData=[c,o] }}) = displaySingle $ (showCol c) ++ " == "++(showCol o)++"[f(0)..f("++(show n)++"-1)]"
  displayer (EGEdge { egeCons = EGCat, egeLinks =  EGTypeData { colData=[c,a,b] }}) = displaySingle $ (showCol c) ++ " == "++(showCol a)++"++"++(showCol b)
  displayer (EGEdge { egeCons = EGAnd, egeLinks =  EGTypeData { boolData=[c,a,b] }}) = displaySingle $ (showBool c) ++ " == "++(showBool a)++" && "++(showBool b)
  displayer (EGEdge { egeCons = EGOr, egeLinks =  EGTypeData { boolData=[c,a,b] }}) = displaySingle $ (showBool c) ++ " == "++(showBool a)++" || "++(showBool b)
  displayer (EGEdge { egeCons = EGEquiv, egeLinks =  EGTypeData { boolData=[c,a,b] }}) = displaySingle $ (showBool c) ++ " == ("++(showBool a)++" == "++(showBool b)++")"
  displayer (EGEdge { egeCons = EGNot, egeLinks =  EGTypeData { boolData=[c,a] }}) = displaySingle $ (showBool c) ++ " == !"++(showBool a)
  displayer (EGEdge { egeCons = EGEqual, egeLinks =  EGTypeData { boolData=[r], intData=[a,b] }}) = displaySingle $ (showBool r) ++ " == ("++(showInt a)++" == "++(showInt b)++")"
  displayer (EGEdge { egeCons = EGDiff, egeLinks =  EGTypeData { boolData=[r], intData=[a,b] }}) = displaySingle $ (showBool r) ++ " == ("++(showInt a)++" != "++(showInt b)++")"
  displayer (EGEdge { egeCons = EGLess q, egeLinks =  EGTypeData { boolData=[r], intData=[a,b] }}) = displaySingle $ (showBool r) ++ " == ("++(showInt a)++(if q then " < " else " <= ")++(showInt b)++")"
  displayer (EGEdge { egeCons = EGAll s _ _, egeLinks = EGTypeData { boolData=r:ab, intData=ai, colData=c:ac }}) = DisplayData ((showBool r)++" == forall("++(showCol c)++") "++(showLst showBool ab)++" "++(showLst showInt ai)++" "++(showLst showCol ac),[displayer s])
  displayer (EGEdge { egeCons = EGAny s _ _, egeLinks = EGTypeData { boolData=r:ab, intData=ai, colData=c:ac }}) = DisplayData ((showBool r)++" == forany("++(showCol c)++") "++(showLst showBool ab)++" "++(showLst showInt ai)++" "++(showLst showCol ac),[displayer s])
--  displayer (EGEdge { egeCons = EGAllC s _ _, egeLinks = EGTypeData { boolData=r:ab, intData=l:h:ai, colData=ac }}) = DisplayData ((showBool r)++" == forall("++(showInt l)++".."++(showInt h)++") "++(showLst showBool ab)++" "++(showLst showInt ai)++" "++(showLst showCol ac),[displayer s])
--  displayer (EGEdge { egeCons = EGAnyC s _ _, egeLinks = EGTypeData { boolData=r:ab, intData=l:h:ai, colData=ac }}) = DisplayData ((showBool r)++" == forany("++(showInt l)++".."++(showInt h)++") "++(showLst showBool ab)++" "++(showLst showInt ai)++" "++(showLst showCol ac),[displayer s])
  displayer (EGEdge { egeCons = EGMap s _, egeLinks = EGTypeData { boolData=ab, intData=ai, colData=r:c:ac }}) = DisplayData ((showCol r)++" == map("++(showCol c)++") "++(showLst showBool ab)++" "++(showLst showInt ai)++" "++(showLst showCol ac),[displayer s])
  displayer (EGEdge { egeCons = EGSlice s _, egeLinks = EGTypeData { boolData=ab, intData=n:ai, colData=r:c:ac }}) = DisplayData ((showCol r)++" == slice("++(showCol c)++",0..("++(showInt n)++")-1) "++(showLst showBool ab)++" "++(showLst showInt ai)++" "++(showLst showCol ac),[displayer s])
  displayer (EGEdge { egeCons = EGFold s _, egeLinks = EGTypeData { boolData=ab, intData=r:i:ai, colData=c:ac }}) = DisplayData ((showInt r)++" == fold("++(showCol c)++","++(showInt i)++") "++(showLst showBool ab)++" "++(showLst showInt ai)++" "++(showLst showCol ac),[displayer s])
  displayer (EGEdge { egeCons = EGCondInt, egeLinks = EGTypeData { boolData=[c], intData=[r,t,f] }}) = displaySingle $ (showInt r) ++ " = (if " ++ (showBool c) ++" then (" ++ (showInt t) ++ ") else (" ++ (showInt f)++"))"
  displayer (EGEdge { egeCons = EGCondEqual, egeLinks = EGTypeData { boolData=[c,a,b] }}) = displaySingle $ "if " ++ (showBool c) ++" then " ++ (showBool a) ++ "=="++(showBool b)
  displayer (EGEdge { egeCons = c })  = DisplayData ("???("++(show c)++")",[])

externMap :: EGModel -> EGTypeData (Map Int EGVarId)
externMap md = foldr f (baseTypeData Map.empty) $ map snd $ Map.toList $ egmEdges md
  where f :: EGEdge -> EGTypeData (Map Int EGVarId) -> EGTypeData (Map Int EGVarId)
        f (EGEdge { egeCons = EGIntExtern i, egeLinks = EGTypeData { intData = [v] } }) st = egTypeMod EGIntType st $ \m -> Map.insert i v m
        f (EGEdge { egeCons = EGBoolExtern i, egeLinks = EGTypeData { boolData = [v] } }) st = egTypeMod EGBoolType st $ \m -> Map.insert i v m
        f (EGEdge { egeCons = EGColExtern i, egeLinks = EGTypeData { colData = [v] } }) st = egTypeMod EGColType st $ \m -> Map.insert i v m
        f _ st = st

emptyModel :: EGModel -> Bool
emptyModel mod = 
  let mm = externMap mod
      ss = Map.size (intData mm) + Map.size (colData mm) + Map.size (boolData mm)
      in ss == (Map.size $ egmEdges mod)

data EGModel = EGModel {
  egmParams :: EGTypeData Int,
  egmVars :: EGTypeData Int,
  egmNEdges :: Int,
  egmEdges :: Map EGEdgeId EGEdge,
  egmLinks :: EGTypeData (Map EGVarId [(EGEdgeId,Int)])
} deriving (Eq,Show)

filterModel :: EGModel -> (EGEdge -> Maybe a) -> (EGModel,[a])
filterModel mod f = foldl ff (mod,[]) $ Map.toList $ egmEdges mod
  where ff (mm,n) (id,ed) = 
           let res = f ed
               in case res of
                 Nothing -> (mm,n)
                 Just a -> (delEdge id mm,a:n)

prefix :: String -> DisplayData -> DisplayData
prefix s (DisplayData (s1,x)) = DisplayData (s++s1,x)

instance Display EGModel where
  displayer (EGModel { egmEdges = x }) = DisplayData ("EGModel",map (\(id,x) -> prefix ((show $ unEGEdgeId id)++": ") $ displayer x) $ Map.toList x)

addEdge :: EGConstraintSpec -> EGTypeData [EGVarId] -> EGModel -> EGModel
addEdge cons links model = 
  if (expected == getConsArgs cons)
    then
      let newEdgeId = EGEdgeId $ egmNEdges model
          in model {
               egmNEdges = egmNEdges model + 1,
               egmEdges = Map.insert newEdgeId (EGEdge { egeCons = cons, egeLinks = links }) $ egmEdges model,
               egmLinks = egTypeDataMap $ \f -> 
                 foldr (\i ->
                     Map.insertWith (++) ((f links) !! i) [(newEdgeId,i)]
                   ) (f $ egmLinks model) [0..(length (f links) - 1)]
             }
    else
      error $ "incorrect number of arguments for constraint ("++(show cons)++")"
  where expected = egTypeDataMap (\f -> length $ f links)

unifyIds :: EGVarId -> EGVarId -> EGVarId -> EGVarId
-- unifyIds fromId toId = (\x -> if x>fromId then x-1 else x) . (\x -> if x==fromId then toId else x)
unifyIds fromId toId = \x -> if x==fromId then toId else x

delEdge :: EGEdgeId -> EGModel -> EGModel
delEdge id mod = do
  let fnd = Map.lookup id $ egmEdges mod
  case fnd of
    Nothing -> error "deleting inexisting edge"
    Just ff -> do
      let nmp = Map.delete id $ egmEdges mod
          mif [] = Nothing
          mif x = Just x
          afn = mif . filter ((/=id) . fst)
          nln = egTypeDataMap $ \f -> foldr (\vid pre -> Map.alter (\(Just x) -> afn x) vid pre) (f $ egmLinks mod) $ f $ egeLinks ff
      mod { egmEdges = nmp, egmLinks = nln }

findEdge :: EGModel -> EGVarType -> EGVarId -> (Int -> Bool) -> (EGConstraintSpec -> Bool) -> Maybe (EGEdgeId,EGEdge)
findEdge model typ varid pos cons =
  let mtc1 = Map.findWithDefault [] varid $ egTypeGet typ $ egmLinks model
      mtc2 = filter (\(_,p) -> pos p) mtc1
      mtc3 = map (\(id,_) -> 
        (id,case Map.lookup id (egmEdges model) of
          Nothing -> error $ "cannot find edge id="++(show id)
          Just xx -> xx
        )) mtc2
      mtc4 = filter (\(_,s) -> cons $ egeCons s) mtc3
      in case mtc4 of
        [] -> Nothing
        a:_ -> Just a

pruneNodes :: EGModel -> EGModel
pruneNodes mod = 
  mod { egmLinks = egTypeDataMap $ \f -> Map.fromList $ filter (\(_,v) -> case v of [] -> True; _ -> False) $ Map.toList $ f $ egmLinks mod }

unifyNodes :: EGVarType -> EGVarId -> EGVarId -> EGModel -> EGModel
unifyNodes vt fromId toId model = model {
--  egmVars = egTypeMod vt (egmVars model) pred,
  egmEdges = Map.map (\x -> x {
    egeLinks = egTypeMod vt (egeLinks x) $ \z -> 
      map (unifyIds fromId toId) z
  }) $ egmEdges model,
  egmLinks = egTypeMod vt (egmLinks model) $ \x -> Map.insertWith (++) toId (Map.findWithDefault [] fromId x) x
}

addNode :: EGVarType -> EGModel -> (EGVarId,EGModel)
addNode vt model = (
    EGVarId (egTypeGet vt $ egmVars model),
    model {
      egmVars = egTypeMod vt (egmVars model) succ
    }
  )

delNode :: EGVarType -> EGVarId -> EGModel -> EGModel
delNode vt id model = model { egmLinks = egTypeMod vt (egmLinks model) (Map.delete id) }

baseGraph :: EGModel
baseGraph = EGModel {
  egmParams = baseTypeData 0,
  egmVars = baseTypeData 0,
  egmNEdges = 0,
  egmEdges = Map.empty,
  egmLinks = baseTypeData Map.empty
}

data DisplayData = DisplayData (String,[DisplayData])

class Display a where
  display :: Int -> a -> String
  displayer :: a -> DisplayData
  display n x = display n $ displayer x

present :: Display a => a -> String
present = display 0

instance Display DisplayData where
  displayer = id
  display n (DisplayData (dir,sub)) = foldl (++) ((replicate (n*2) ' ')++dir++"\n") $ map (display $ n+1) sub

displaySingle :: String -> DisplayData
displaySingle x = DisplayData (x,[])

getConnectedEdges :: EGModel -> EGVarType -> EGVarId -> [(EGEdge,Int)]
getConnectedEdges model typ id = map (\(eid,pos) -> (fromJust $ Map.lookup eid $ egmEdges model, pos)) $ fromJust $ Map.lookup id $ egTypeGet typ $ egmLinks model
