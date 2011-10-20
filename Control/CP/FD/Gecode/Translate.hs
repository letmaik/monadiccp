-- optimalisaties: zie http://www.cs.mu.oz.au/~pjs/papers/padl2008.pdf
-- zie ook http://www.cs.mu.oz.au/~pjs/papers/constraints08b.pdf
-- mcp paper: http://www.cs.kuleuven.be/~toms/Research/papers/monadic_cp_draft.pdf

module Control.CP.FD.Gecode.Translate (
  generate_gecode
) where

import Maybe (fromJust,isNothing,isJust)
import List (findIndex)
import Data.Map (elems,Map,lookup)

import Control.CP.FD.Gecode.CodegenSolver
import Control.CP.FD.Gecode.Common
import Control.CP.Solver

--------------------------------------------------------------------------------
-- Main compilation function
--------------------------------------------------------------------------------

generate_gecode = stateToProg . compile
-- generate_gecode = show . compile

--------------------------------------------------------------------------------
-- Implementation
--------------------------------------------------------------------------------

countTypeVars :: Store -> GType -> Int -> Int
countTypeVars s t u = foldl (+) 0 $ map (\x -> 1) $ filter (\x -> (u<0 || x<u) && (t == getVarType s x)) $ varsUsed (ctree s) []


maxDepth :: StoreNode -> Int
maxDepth (StoreNode { cons=_, dis=SNLeaf}) = 1
maxDepth (StoreNode { cons=_, dis=SNIntl l r }) = 1 + (maxDepth l `max` maxDepth r)

typeList = [TypeBool, TypeInt]

varsUsed :: StoreNode -> [ Bool ] -> [ Int ]
varsUsed node path = (nvars node) ++ case (dis node,path) of
  (SNLeaf,_) -> []
  (SNIntl l _,[]) -> (varsUsed l [])
  (SNIntl l _,False:o) -> varsUsed l o
  (SNIntl _ r,True:o)  -> varsUsed r o

typeToString :: GType -> String
typeToString TypeInt = "IntVar"
typeToString TypeBool = "BoolVar"

typeToDefArgs :: GType -> (String,String)
typeToDefArgs TypeInt = ("-1000000000","1000000000")
typeToDefArgs TypeBool = ("0","1")

getVarName :: Store -> String -> Int -> String
getVarName s pre i = pre ++ "bb" ++ (typeToString $ getVarType s i) ++ "[" ++ (show $ countTypeVars s (getVarType s i) i) ++ "]"

getName :: GTerm t => Store -> String -> t -> String
getName s pre v = case (getVarId v) of
  Nothing -> case (getIntValue v) of
    Nothing -> error "oei"
    Just n -> show n
  Just i -> getVarName s pre i

stateToExplList :: Store -> [ (String,String,String) ]
stateToExplList s = map (fm) $ filter (\x -> not $ isVarImplicit s x) $ [0..((vars s)-1)]
    where fm i = (typeToString $ getVarType s i,"v"++(show i),getVarName s "" i)

stateToConstList :: Store -> Map Int VarBound -> [ String ]
stateToConstList s b = map fm $ elems $ b
    where fm (VarBound i l u) = (getVarName s "" i) ++ "(*this," ++ (if isJust l then show $ fromJust l else defl) ++ "," ++ (if isJust u then show $ fromJust u else defu) ++ ")"
            where (defl,defu) = typeToDefArgs $ getVarType s i

gopToGCRel :: GOperator -> String
gopToGCRel OEqual = "IRT_EQ"
gopToGCRel ODiff = "IRT_NQ"
gopToGCRel OLess = "IRT_LE"

gopToInvGCRel :: GOperator -> String
gopToInvGCRel OEqual = "IRT_EQ"
gopToInvGCRel ODiff = "IRT_NQ"
gopToInvGCRel OLess = "IRT_GR"

stateToPostList :: Store -> [ GConstraint ] -> [ String ]
stateToPostList s c = map fm $ reverse $ c
    where fm (CRel t1 o t2) = "rel(home," ++ (gn t1) ++ "," ++ (gopToGCRel o) ++ "," ++ (gn t2) ++ ")"
          fm (CMult t1 t2 t3) = "mult(home," ++ (gn t1) ++ "," ++ (gn t2) ++ "," ++ (gn t3) ++ ")"
          fm (CDiv t1 t2 t3) = "div(home," ++ (gn t1) ++ "," ++ (gn t2) ++ "," ++ (gn t3) ++ ")"
          fm (CMod t1 t2 t3) = "mod(home," ++ (gn t1) ++ "," ++ (gn t2) ++ "," ++ (gn t3) ++ ")"
          fm (CAbs t1 t2) = "abs(home," ++ (gn t1) ++ "," ++ (gn t2) ++ ")"
          fm (CDom t l u) = "dom(home," ++ (gn t) ++ "," ++ (show l) ++ "," ++ (show u) ++ ")"
          fm (CValue t v) = "rel(home," ++ (gn t) ++ ",IRT_EQ," ++ (show v) ++ ")"
	  fm (CLinear l o c) = case (c,l) of
            (0,[(v1,a),(v2,b)]) | a+b==0 && a>0 -> "rel(home," ++ (gn v1) ++ "," ++ (gopToGCRel o) ++ "," ++ (gn v2) ++ ")"
            (0,[(v1,a),(v2,b)]) | a+b==0 && a<0 -> "rel(home," ++ (gn v1) ++ "," ++ (gopToInvGCRel o) ++ "," ++ (gn v2) ++ ")"
	    (_,[(v1,a)]) | a>0 && ((c `mod` a)==0) -> "rel(home," ++ (gn v1) ++ "," ++ (gopToGCRel o) ++ "," ++ (show (c `div` a)) ++ ")"
	    (_,[(v1,a)]) | a<0 && ((c `mod` (-a))==0) -> "rel(home," ++ (gn v1) ++ "," ++ (gopToInvGCRel o) ++ "," ++ (show (c `div` a)) ++ ")"
	    (_,l) | all (\(_,a) -> a==1) l -> case unzip l of
              (x,a) -> "{ " ++ (bl "iva" x) ++ " linear(home,iva," ++ (gopToGCRel o) ++ "," ++ (show c) ++ "); }"
            _ -> case unzip l of
              (x,a) -> "{ IntArgs ia(" ++ (show $ length a) ++ (foldl (\x y -> x ++ "," ++ (show y)) "" a) ++ "); "++(bl "iva" x) ++ " linear(home,ia,iva," ++ (gopToGCRel o) ++ "," ++ (show c) ++ "); }"
          fm (CAllDiff l) = "{ " ++ (bl "ia" l) ++ "; distinct(home,ia); }"
          fm (CSorted l e) = "{ " ++ (bl "ia" l) ++ "; rel(home,ia,"++(if e then "IRT_LQ" else "IRT_LE")++"); }"
          gn t = getName s "p->" t
          bl n l = "IntVarArgs "++n++"(" ++ (show $ length l) ++ "); " ++ (foldl (++) "" (map (\i -> n++"[" ++ (show i) ++ "]=" ++ (getVarName s "p->" $ fromJust $ getVarId $ l !! i) ++ "; ") [0..(length l)-1]))

stateToBranchList :: Store -> GType -> [ String ]
stateToBranchList s t = map fm $ filter ff $ [0..((vars s)-1)]
    where ff i = (not $ isVarImplicit s i) && (t == getVarType s i)
          fm i = getVarName s "" i

stateToBranchCode s t = "    " ++ tn ++ "Args b" ++ tn ++ "(" ++ (show (length vars)) ++ ");\n" ++ (
    foldl (\x y -> x ++ "    b" ++ tn ++ "[" ++ (show y) ++ "]=" ++ (vars !! y) ++ ";\n") "" [0..(length vars)-1]) ++
    "    branch(*this, b"++tn++", INT_VAR_SIZE_MIN, INT_VAL_SPLIT_MIN);\n"
	where tn = typeToString t
              vars = stateToBranchList s t

stateToBranches s = foldl (++) [] $ map (stateToBranchCode s) typeList

-- countExplicits :: Store -> GType -> Int
-- countExplicits s t = foldl (+) 0 $ map (\x -> if isVarImplicit s x then 0 else 1) $ filter (\x -> t == getVarType s x) $ varsUsed (ctree s) []

nodeToProg :: Store -> Map Int VarBound -> StoreNode -> [ Bool ] -> String
nodeToProg store bnds node path = 
    "  static void node" ++ pathS ++ "(Space &home) {\n" ++
    "  /* varsused" ++ (show vrs) ++ "*/\n" ++
    "    HaskellProg *p = (HaskellProg *)(&home);\n" ++
    (foldl (\x y -> x ++ "    " ++ y ++ ";\n") "" $ map (\x -> (getVarName store "p->" x)++".init(home,"++(lowest x)++","++(highest x)++")") $ nvars node) ++
    (foldl (\x y -> x ++ "    " ++ y ++ ";\n") "" $ stateToPostList store $ cons node) ++
    (case dis node of 
      SNLeaf -> (foldl (++) "" $ map (\x -> "    rel(home,p->i["++(show x)++"],IRT_EQ,0);\n") [(length path)..(maxDepth $ ctree store)-2]) ++ 
                 (foldl (++) "" $ map (\x -> "    rel(home," ++ (getVarName store "p->" x) ++ ",IRT_EQ,"++(lowest x)++");\n") $ filter (\x -> isNothing $ findIndex (== x) vrs) [0..(vars store)-1])
      SNIntl _ _ -> "    when(home,p->i[" ++ lenS ++ "],&node"++pathS++"R,&node"++pathS++"L);\n"
    ) ++
    "  }\n" ++
    (case (dis node) of
      SNLeaf -> ""
      SNIntl l r -> nodeToProg store bnds l (path ++ [ False ]) ++ nodeToProg store bnds r (path ++ [ True ])
    )
    where pathS = foldl (++) "" $ map (\x -> if x then "R" else "L") path
          lenS = show $ length path
	  vrs = varsUsed (ctree store) path
          lowest i = case Data.Map.lookup i bnds of
            Nothing -> case typeToDefArgs $ getVarType store i of
              (x,_) -> x
            Just (VarBound _ Nothing _) -> case typeToDefArgs $ getVarType store i of
              (x,_) -> x
            Just (VarBound _ (Just l) _) -> show l
          highest i = case Data.Map.lookup i bnds of
            Nothing -> case typeToDefArgs $ getVarType store i of
              (_,x) -> x
            Just (VarBound _ _ Nothing) -> case typeToDefArgs $ getVarType store i of
              (_,x) -> x
            Just (VarBound _ _ (Just l)) -> show l
            

stateToProg :: Store -> String
stateToProg s = 
    "#include \"gecode/kernel.hh\"\n"++
    "#include \"gecode/support.hh\"\n"++ 
    "#include \"gecode/int.hh\"\n"++
    "#include \"gecode/search.hh\"\n"++
    "#include \"gecode/minimodel.hh\"\n"++
    "\n"++
    "using namespace Gecode;\n"++
    "\n"++
    "class HaskellProg : public Space {\n"++
    "protected:\n"++
--    (foldl (\x (y1,y2) -> x ++ "  " ++ y1 ++ " " ++ y2 ++ ";\n") "" (stateToDefList s)) ++ 
    "  BoolVarArray i;\n\n"++
    (foldl (++) "" $ map (\x -> "  " ++ (typeToString x) ++ "Array bb" ++ (typeToString x) ++ ";\n") typeList) ++
    "public:\n"++
    "  HaskellProg() : " ++ 
    (foldl (\x y -> (if x=="" then "" else x ++ ", ") ++ y) "" $ map (\x -> "bb" ++ typeToString x ++ "(*this," ++ (show $ countTypeVars s x (-1)) ++ ")") typeList) ++ 
    ", i(*this,"++(show $ (maxDepth (ctree s)) - 1)++",0,1) {\n"++
    "    node(*this);\n"++
    "    branch(*this, i, INT_VAR_SIZE_MIN, INT_VAL_MIN);\n" ++ stateToBranches s ++
    "  };\n"++
    "  virtual void print(std::ostream& os) {\n"++
    (foldl (\x (vType,vName,vExpr) -> x ++ "    os << \"" ++ vName ++ ": \" << " ++ vExpr ++ " << std::endl;\n") "" (stateToExplList s)) ++
    "  }\n"++
    "  HaskellProg(bool share, HaskellProg &s) : Space(share,s) {\n"++
--    (foldl (\x (vType,vName,vExpr) -> x ++ "    " ++ vExpr ++ ".update(*this, share, s." ++ vExpr ++ ");\n") "" (stateToExplList s)) ++
    "    i.update(*this,share,s.i);\n" ++
    (foldl (\x y -> x ++ "    " ++ y ++ ";\n") "" $ map (\x -> "bb" ++ (typeToString x) ++ ".update(*this,share,s.bb"++(typeToString x)++")") typeList) ++
    "  }\n"++
    "  virtual Space* copy(bool share) {\n"++
    "    return new HaskellProg(share, *this);\n"++
    "  }\n"++
    nodeToProg s bounds (ctree s) [] ++
    "};\n"++
    "\n"++
    "int main(void) {\n"++
    "  HaskellProg *prog=new HaskellProg();\n"++
    "  DFS<HaskellProg> srch(prog);\n"++
    "  delete prog;\n"++
    "  do {\n"++
    "    HaskellProg *sol=srch.next();\n"++
    "    if (sol==NULL) break;\n"++
    "    sol->print(std::cout);\n"++
    "  } while(0);\n"++
    "  return 0;\n"++
    "}\n"
    where bounds = getAllBounds s
          vrs = varsUsed (ctree s) []
