{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.CP.FD.Gecode.CodegenSolver (
  generateGecode,
  CodegenGecodeSolver,
  CodegenGecodeOptions(..), setOptions,
) where

import Data.Char (ord,chr)
import Data.Maybe (fromJust,isJust)
import Data.Map (Map)
import Data.Maybe (isNothing)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Lazy
import Control.Monad.Trans

import Language.CPP.Syntax.AST
import Language.CPP.Pretty

import Control.CP.Debug
import Control.CP.Solver
import Control.CP.SearchTree
import Control.CP.EnumTerm
import Control.CP.FD.FD
import Data.Expr.Data
import Data.Expr.Sugar
-- import Control.CP.FD.Expr.Util
import Control.CP.FD.Model
import Control.CP.FD.Gecode.Common
import Control.CP.FD.SearchSpec.Data
import Data.Linear

import Control.Search.Generator
import Control.Search.Stat
import Control.Search.Constraints
import Control.Search.Combinator.And
import Control.Search.Combinator.Base as Base
import Control.Search.Combinator.Misc
import Control.Search.Combinator.Print
import Control.Search.Combinator.Until
import Control.Search.Combinator.Once
import Control.Search.Combinator.Or

idx s c i = 
  if i<0 
    then error ("GC:CG idx("++s++"): i="++(show i)++"<0")
    else if i>=length c
      then error ("GC:CG idx("++s++"): i="++(show i)++">=(length c)="++(show $ c))
      else c!!i

data ColDef =
    ColDefSize GecodeIntConst
  | ColDefList [IntVar]
  | ColDefCat ColVar ColVar
--  | ColDefTake ColVar GecodeIntConst GecodeIntConst
  | ColDefConstMap GecodeListConst (GecodeCIFn CodegenGecodeSolver)
  deriving (Show)

data IntParDef =
    IntParDefExt Int
  | IntParDefCPP CPPExpr
  deriving (Show)

data ColParDef =
    ColParDefExt Int
  | ColParDefCPP CPPExpr
  deriving (Show)

data CodegenGecodeState = CodegenGecodeState {
  nIntVars :: Int,
  nBoolVars :: Int,
  nIntPars :: Int,
  intPars :: [IntParDef],
  nColPars :: Int,
  colPars :: [ColParDef],
  colVars :: [ColDef],
  colList :: [GecodeColConst],
  colListEnt :: Map GecodeColConst Int,
  cons :: [GecodeConstraint CodegenGecodeSolver],
  intRet :: Set IntVar,
  boolRet :: Set BoolVar,
  colRet :: Set ColVar,
  level :: Int,
  parent :: Maybe CodegenGecodeState,
  options :: CodegenGecodeOptions,
  searchSpec :: Maybe (SearchSpec IntVar ColVar BoolVar)
} deriving (Show)


data CodegenGecodeOptions = CodegenGecodeOptions {
  noTrailing :: Bool,
  noGenSearch :: Bool
} deriving (Show)

initOptions :: CodegenGecodeOptions
initOptions = CodegenGecodeOptions {
  noTrailing = False,
  noGenSearch = False
}

initState :: CodegenGecodeState
initState = CodegenGecodeState { 
  nIntVars = 0,
  nBoolVars = 0,
  nIntPars = 0,
  intPars = [],
  nColPars = 0,
  colPars = [],
  colVars = [],
  colList = [],
  colListEnt = Map.empty,
  cons = [],
  intRet = Set.empty,
  boolRet = Set.empty,
  colRet = Set.empty,
  level = 0,
  parent = Nothing,
  options = initOptions,
  searchSpec = Nothing
}

newIntParam :: CodegenGecodeSolver Int
newIntParam = do
  s <- get
  let n = nIntPars s
  let r = length $ intPars s
  put $ s { nIntPars = n+1, intPars = (intPars s)++[IntParDefExt n] }
  return r

newColParam :: CodegenGecodeSolver Int
newColParam = do
  s <- get
  let n = nColPars s
  let r = length $ colPars s
  put $ s { nColPars = n+1, colPars = (colPars s)++[ColParDefExt n] }
  return r

newtype CodegenGecodeSolver a = CodegenGecodeSolver { cgsState :: State CodegenGecodeState a }
  deriving (Monad, MonadState CodegenGecodeState)

instance Solver CodegenGecodeSolver where
  type Constraint CodegenGecodeSolver = GecodeConstraint CodegenGecodeSolver
  type Label CodegenGecodeSolver = ()
  run p = evalState (cgsState p) initState
  mark = return ()
  goto s = error "returning to a previous state is not supported yet"
  add c = do
    s <- get
    put $ s { cons = c:cons s }
    return True

setOptions :: (CodegenGecodeOptions -> CodegenGecodeOptions) -> CodegenGecodeSolver ()
setOptions f = do
  s <- get
  put $ s { options = f $ options s }

data IntVar = 
    IntVar Int Int    -- IntVar level id
  | IntVarIdx ColVar GecodeIntConst 
  | IntVarCPP (CPPExpr -> CPPExpr)
  | IntVarCond GecodeBoolConst IntVar IntVar
  deriving (Eq,Ord,Show)
data BoolVar = 
    BoolVar Int Int   -- BoolVar level id
  | BoolVarCPP (CPPExpr -> CPPExpr)
  deriving (Eq,Ord,Show)
data ColVar = ColVar Int Int  -- ColVar level id
  deriving (Eq,Ord,Show)

instance Eq (CPPExpr -> CPPExpr) where
  a==b = a astThis == b astThis
instance Ord (CPPExpr -> CPPExpr) where
  compare a b = compare (a astThis) (b astThis)
instance Show (CPPExpr -> CPPExpr) where
  show a = show (a astThis)

genVar :: String -> CodegenGecodeState -> String
genVar s st = 
  case level st of
    0 -> s
    l -> (s ++ show l)

instance Term CodegenGecodeSolver IntVar where
  newvar = do
    s <- get
    let ni = nIntVars s
    put $ s { nIntVars = ni+1 }
    return $ IntVar (level s) ni
  type Help CodegenGecodeSolver IntVar = ()
  help _ _ = ()

instance Term CodegenGecodeSolver BoolVar where
  newvar = do
    s <- get
    let ni = nBoolVars s
    put $ s { nBoolVars = ni+1 }
    return $ BoolVar (level s) ni
  type Help CodegenGecodeSolver BoolVar = ()
  help _ _ = ()

defineCol :: ColDef -> CodegenGecodeSolver ColVar
defineCol def = do
    s <- get
    let ni = length $ colVars s
    put $ s { colVars = colVars s ++ [def] }
    return $ ColVar (level s) ni

colSize :: ColVar -> CodegenGecodeState -> GecodeIntConst
colSize (cc@(ColVar l c)) s = 
  if (level s == l)
    then debug ("colSize (ColVar l="++(show l)++" c="++(show c)++")") $ case idx "colSize" (colVars s) c of
      ColDefSize s -> s
      ColDefList l -> Const $ toInteger $ length l
      ColDefCat c1 c2 -> colSize c1 s + colSize c2 s
--      ColDefTake _ _ s -> s
    else colSize cc (fromJust $ parent s)

lstindex :: Eq a => [a] -> [a] -> Maybe Int
lstindex [] _ = Just 0
lstindex _ [] = Nothing
lstindex r@(a:b) (c:d) | a==c = case lstindex b d of
  Nothing -> lstindex r d
  Just p -> Just $ p+1
lstindex a (_:b) = lstindex a b

registerList :: GecodeColConst -> (CodegenGecodeState -> CodegenGecodeState)
registerList l state = case lookupList state l of
  Nothing -> state { colListEnt = Map.insert l (length $ colList state) (colListEnt state), colList = (colList state) ++ [l] }
  Just _ -> state

lookupList :: CodegenGecodeState -> GecodeColConst -> Maybe (Int,Int)
lookupList s col = case Map.lookup col (colListEnt s) of
  Nothing -> case parent s of
    Nothing -> Nothing
    Just p -> lookupList p col
  Just r -> Just (level s,r)

instance GecodeSolver CodegenGecodeSolver where
  type GecodeIntVar CodegenGecodeSolver = IntVar
  type GecodeBoolVar CodegenGecodeSolver = BoolVar
  type GecodeColVar CodegenGecodeSolver = ColVar
  newInt_at c p = return $ IntVarIdx c p
  newInt_cond c t f = return $ IntVarCond c t f
  newCol_size s = defineCol $ ColDefSize s
  newCol_list l = defineCol $ ColDefList l
  newCol_cat c1 c2 = defineCol $ ColDefCat c1 c2
--  newCol_take c p l = defineCol $ ColDefTake c p l
  col_getSize c = do
    state <- get
    return $ colSize c state
  col_regList (ColTerm _) = return ()
  col_regList l = do
    state <- get
    put $ registerList l state
  splitBoolDomain _ = error "cannot split run-time boolean domains"
  splitIntDomain _ = error "cannot split run-time integer domains"

class CompilableModel t where
  specific_compile :: t -> CodegenGecodeSolver ()

instance CompilableModel (CodegenGecodeSolver a) where
  specific_compile x = x >> return ()

resolveVars :: SearchSpec ModelInt ModelCol ModelBool -> FDInstance (GecodeWrappedSolver CodegenGecodeSolver) (SearchSpec IntVar ColVar BoolVar)
resolveVars spec = mmapSearch spec mapInt mapCol mapBool
  where mapCol v = do
          [GCTVar col] <- getColTerm [v] GCSVar
          case col of
            ColVar 0 _ -> liftFD $ liftGC $ do
              s <- get
              put s { colRet = Set.insert col $ colRet s }
              return col
            ColVar _ _ -> error "Non-toplevel array escapes"
        mapInt v = do
          [var] <- getIntTerm [v]
          case var of
            IntVar 0 r -> liftFD $ liftGC $ do
              s <- get
              put s { intRet = Set.insert var $ intRet s }
              return var
            IntVar _ _ -> error "Non-toplevel variable escapes"
            _ -> liftFD $ liftGC $ do
              s <- get
              put s { intRet = Set.insert var $ intRet s }
              return var
        mapBool v = do
          [var] <- getBoolTerm [v]
          case var of
            BoolVar 0 r -> liftFD $ liftGC $ do
              s <- get
              put s { boolRet = Set.insert var $ boolRet s }
              return var
            BoolVar _ _ -> error "Non-toplevel boolean escapes"
            _ -> liftFD $ liftGC $ do
              s <- get
              put s { boolRet = Set.insert var $ boolRet s }
              return var

instance CompilableModel ((FDInstance (GecodeWrappedSolver CodegenGecodeSolver)) ModelCol) where
  specific_compile x = unliftGC $ runFD $ do
    res <- x
    min <- getMinimizeVar
    spec <- resolveVars $ PrintSol [] [res] [] $ case min of
      Nothing -> LimitSolCount 1 $ Labelling $ LabelCol res (Term DDomSize) Minimize (Term DMedian) (\var val -> var @<= val)
      Just m -> BranchBound m Minimize $ CombineSeq (Labelling $ LabelCol res (Term DDomSize) Minimize (Term DMedian) (\var val -> var @<= val)) (Labelling $ LabelInt m (Term DMedian) (\var val -> var @<= val))
    liftFD $ liftGC $ do
      s <- get
      put s { searchSpec = Just spec }

instance CompilableModel ((FDInstance (GecodeWrappedSolver CodegenGecodeSolver)) (SearchSpec ModelInt ModelCol ModelBool)) where
  specific_compile x = unliftGC $ runFD $ do
    res <- x
    y <- resolveVars res
    liftFD $ liftGC $ do
      s <- get
      put s { searchSpec = Just y }

instance CompilableModel m => CompilableModel (ModelInt -> m) where
  specific_compile x = do
    n <- newIntParam
    specific_compile $ x $ Term $ ModelIntPar n

instance CompilableModel m => CompilableModel (ModelCol -> m) where
  specific_compile x = do
    n <- newColParam
    specific_compile $ x $ ColTerm $ ModelColPar n

buildState :: Solver s => Tree s a -> s a
buildState (Add c v) = debug "cgs::buildState.Add" $ 
                         do
                           add c
                           buildState v
buildState (NewVar f) = debug "cgs::buildState.NewVar" $ 
                          do
                            v <- newvar
                            buildState $ f v
buildState (Try l r)  = debug "cgs::buildState.Try" $ buildState l
buildState (Label m) = debug "cgs::buildState.Label" $ m >>= buildState
buildState (Fail) = return $ error "Code generation for failed model"
buildState (Return x) = return x

instance CompilableModel (Tree (FDInstance (GecodeWrappedSolver CodegenGecodeSolver)) ModelCol) where
  specific_compile = specific_compile . buildState

getTopState :: (CodegenGecodeState -> a) -> (CodegenGecodeState -> a)
getTopState f o = case parent o of
  Just p -> getTopState f p
  Nothing -> f o

modTopState :: (CodegenGecodeState -> CodegenGecodeState) -> (CodegenGecodeState -> CodegenGecodeState)
modTopState f o = case parent o of
  Just p -> o { parent = Just $ modTopState f p }
  Nothing -> f o

compile :: CompilableModel m => Bool -> m -> (CodegenGecodeSolver a) -> CodegenGecodeSolver a
compile par x m = do
  s <- get
  case par of
    False -> put $ initState { parent = Nothing, level = 0 }
    True  -> put $ initState { parent = Just s,  level = 1 + level s, intPars = intPars s, colPars = colPars s }
  specific_compile x
  r <- m
  ss <- get
  case parent ss of
    Nothing -> return ()
    Just p  -> put p
  return r

retState :: MonadState s m => m a -> m (a,s)
retState m = do
  r <- m
  s <- get
  return (r,s)

astCompile m = compile True m (astPost >>= return . CPPCompound)

astIncludes = [ "gecode/kernel.hh", "gecode/support.hh", "gecode/int.hh", "gecode/search.hh", "vector", "list" ]

astGenerate :: CodegenGecodeSolver [CPPFile]
astGenerate = do
  s <- get
  tru <- astTranslUnit
  mnu <- case noGenSearch $ options s of
    False -> astMainUnitGen
    True -> astMainUnitDef
  return [
    CPPFile {
      cppMacroStm = [ CPPMacroIncludeUser x | x <- astIncludes ],
      cppUsing = [ "Gecode", "std" ],
      cppTranslUnit = tru
    },
    CPPFile {
      cppMacroStm = [],
      cppUsing = [],
      cppTranslUnit = mnu
    }
   ]

astTInt = CPPTypePrim "int"
astTIV = CPPTypePrim "IntVar"
astTIA = CPPTypePrim "IntArgs"
astTIVA = CPPTypePrim "IntVarArgs"
astTBV = CPPTypePrim "BoolVar"
astTBVA = CPPTypePrim "BoolVarArgs"

astInt :: Integer -> CPPExpr
astInt a = CPPConst $ CPPConstInt a

astThis :: CPPExpr
astThis = CPPUnary CPPOpInd $ CPPVar "this"

astLowerBound = astInt (-1000000000)
astUpperBound = astInt (1000000000)

astColSize :: ColVar -> CodegenGecodeState -> CPPExpr -> CPPExpr
astColSize c state ctx = astIntExpr state ctx $ colSize c state

astIntParam :: CodegenGecodeState -> CPPExpr -> GecodeIntParam -> CPPExpr
astIntParam state ctx (GIParam n) | n<(-1000) = CPPVar $ "___parVar"++(show $ -(n+1000))++"___"
astIntParam state ctx (GIParam i) = case (idx "astIntParam" (intPars state) i) of
  IntParDefExt n -> CPPIndex (call ctx "iP") (astInt $ fromIntegral n)
  IntParDefCPP c -> c

astBoolParam :: CodegenGecodeState -> CPPExpr -> GecodeBoolParam -> CPPExpr
astBoolParam state ctx (GBParam i) = CPPIndex (call ctx "bP") (astInt $ fromIntegral i)

astColParam :: CodegenGecodeState -> CPPExpr -> GecodeColParam -> CPPExpr
astColParam state ctx (GCParam i) = case (idx "astColParam" (colPars state) i) of
  ColParDefExt n -> CPPIndex (call ctx "cP") (astInt $ fromIntegral n)
  ColParDefCPP c -> c 

astBoolExpr :: CodegenGecodeState -> CPPExpr -> GecodeBoolConst -> CPPExpr
astBoolExpr state ctx (BoolTerm par) = astBoolParam state ctx par
astBoolExpr state ctx (BoolConst b) = astInt (if b then 1 else 0)
astBoolExpr state ctx (BoolAnd a b) = CPPBinary (astBoolExpr state ctx a) CPPOpLAnd (astBoolExpr state ctx b)
astBoolExpr state ctx (BoolOr a b) = CPPBinary (astBoolExpr state ctx a) CPPOpLOr (astBoolExpr state ctx b)
astBoolExpr state ctx (BoolNot a) = CPPUnary CPPOpNeg (astBoolExpr state ctx a)
astBoolExpr state ctx (Rel a EREqual b) = CPPBinary (astIntExpr state ctx a) CPPOpEq (astIntExpr state ctx b)
astBoolExpr state ctx (Rel a ERDiff b) = CPPBinary (astIntExpr state ctx a) CPPOpNeq (astIntExpr state ctx b)
astBoolExpr state ctx (Rel a ERLess b) = CPPBinary (astIntExpr state ctx a) CPPOpLe (astIntExpr state ctx b)
astBoolExpr state ctx (BoolEqual a b) = CPPBinary (astBoolExpr state ctx a) CPPOpEq (astBoolExpr state ctx b)
astBoolExpr state ctx (BoolCond c t f) = CPPCond (astBoolExpr state ctx c) (Just $ astBoolExpr state ctx t) (astBoolExpr state ctx f)
astBoolExpr state ctx x = error $ "astBoolExpr(" ++ (show x) ++ ")"

astColExpr :: CodegenGecodeState -> CPPExpr -> GecodeColConst -> GecodeIntConst -> CPPExpr
astColExpr state ctx (ColTerm par) pos = CPPIndex (astColParam state ctx par) (astIntExpr state ctx pos)
astColExpr state ctx (ColList lst) (Const pos) = astIntExpr state ctx (lst!!(fromInteger pos))
astColExpr state ctx c p = case lookupList state c of
  Nothing -> error $ "Unregistered constant list used: " ++ (show c)
  Just (l,n) -> CPPIndex (CPPVar ("cte" ++ show l ++ "_" ++ show n)) (astIntExpr state ctx p)
astIntExpr :: CodegenGecodeState -> CPPExpr -> GecodeIntConst -> CPPExpr
astIntExpr state ctx (Term par) = astIntParam state ctx par
astIntExpr state _ (Const i) = astInt i
astIntExpr state ctx (Plus a b) = CPPBinary (astIntExpr state ctx a) CPPOpAdd (astIntExpr state ctx b)
astIntExpr state ctx (Minus a b) = CPPBinary (astIntExpr state ctx a) CPPOpSub (astIntExpr state ctx b)
astIntExpr state ctx (Mult a b) = CPPBinary (astIntExpr state ctx a) CPPOpMul (astIntExpr state ctx b)
astIntExpr state ctx (Div a b) = CPPBinary (astIntExpr state ctx a) CPPOpDiv (astIntExpr state ctx b)
astIntExpr state ctx (Mod a b) = CPPBinary (astIntExpr state ctx a) CPPOpRmd (astIntExpr state ctx b)
astIntExpr state ctx (Abs a) = CPPCall (CPPVar "abs") [astIntExpr state ctx a]
astIntExpr state ctx (At c a) = astColExpr state ctx c a
astIntExpr state ctx (ColSize (ColTerm (GCParam i))) = CPPIndex (call ctx "cPs") (astInt $ toInteger i)
astIntExpr state ctx (Channel b) = astBoolExpr state ctx b
astIntExpr state ctx (Cond c a b) = CPPCond (astBoolExpr state ctx c) (Just $ astIntExpr state ctx a) (astIntExpr state ctx b)

astDecl :: String -> CPPType -> CPPDecl
astDecl name typ = CPPDecl { cppDeclName=Just name, cppType=typ, cppTypeQual=[], cppTypeStor=[], cppDeclInit=Nothing }
astDeclEq :: String -> CPPType -> CPPExpr -> CPPDecl
astDeclEq name typ val = CPPDecl { cppDeclName=Just name, cppType=typ, cppTypeQual=[], cppTypeStor=[], cppDeclInit=Just $ CPPInitValue val }
astDeclEqA :: String -> CPPType -> [CPPExpr] -> CPPDecl
astDeclEqA name typ val = CPPDecl { cppDeclName=Just name, cppType=typ, cppTypeQual=[], cppTypeStor=[], cppDeclInit=Just $ CPPInitArray val }
astDeclFn :: String -> CPPType -> [CPPExpr] -> CPPDecl
astDeclFn name typ val = CPPDecl { cppDeclName=Just name, cppType=typ, cppTypeQual=[], cppTypeStor=[], cppDeclInit=Just $ CPPInitCall val }

call :: CPPExpr -> String -> CPPExpr
call (CPPUnary CPPOpInd (CPPVar "this")) f = CPPVar f
call (CPPUnary CPPOpInd x) f = CPPMember x f True
call x f = CPPMember x f False

unvar (CPPVar s) = s
unvar x = error $ "Unvarring " ++ show x

instance Num CPPExpr where
  a + b = CPPBinary a CPPOpAdd b
  a * b = CPPBinary a CPPOpMul b
  a - b = CPPBinary a CPPOpSub b
  negate a = CPPUnary CPPOpMinus a
  abs a = CPPCall (CPPVar "abs") [a]
  signum a = CPPCall (CPPVar "signum") [a]
  fromInteger a = astInt a

astLinOperator GOEqual     _     = CPPVar "IRT_EQ"
astLinOperator GODiff      _     = CPPVar "IRT_NQ"
astLinOperator GOLess      False = CPPVar "IRT_LE"
astLinOperator GOLess      True  = CPPVar "IRT_GR"
astLinOperator GOLessEqual False = CPPVar "IRT_LQ"
astLinOperator GOLessEqual True  = CPPVar "IRT_GQ"

astReifList _ _ Nothing = []
astReifList state ctx (Just b) = [astBoolVar state ctx b]

varName s l n = s ++ (if l==0 then "" else show l) ++ "_" ++ (show n)
boolVarName (BoolVar l n) = varName "bV" l n
colVarName (ColVar l n) = varName "cV" l n
intVarName (IntVar l n) = varName "iV" l n

astBoolExt state r | (Set.member r $ boolRet state)  = True
astBoolExt _ _ = False
astColExt state r | (Set.member r $ colRet state)  = True
astColExt _ _ = False
astIntExt state r | (Set.member r $ intRet state)  = True
astIntExt _ _ = False

astBoolVar :: CodegenGecodeState -> CPPExpr -> BoolVar -> CPPExpr
astBoolVar state ctx q@(BoolVar 0 r) | (Set.member q $ boolRet state) = call ctx ("bR" ++ show r)
astBoolVar state ctx (BoolVarCPP f) = f ctx
astBoolVar state ctx (v@(BoolVar l _)) | (l < level state) = astBoolVar (fromJust $ parent state) ctx v
astBoolVar state ctx b = CPPVar $ boolVarName b

astIntVar :: CodegenGecodeState -> CPPExpr -> IntVar -> CPPExpr
astIntVar state ctx (IntVarCond c t f) = CPPCond (astBoolExpr state ctx c) (Just $ astIntVar state ctx t) (astIntVar state ctx f)
astIntVar state ctx (IntVarCPP f) = f ctx
astIntVar state ctx (IntVarIdx c p) = CPPIndex (astColVar state ctx c) (astIntExpr state ctx p)
astIntVar state ctx q@(IntVar 0 r) | (Set.member q $ intRet state) = call ctx ("iR" ++ show r)
astIntVar state ctx (v@(IntVar l _)) | (l < level state) = astIntVar (fromJust $ parent state) ctx v
astIntVar state ctx i = CPPVar $ intVarName i

astColVar :: CodegenGecodeState -> CPPExpr -> ColVar -> CPPExpr
astColVar state ctx q@(ColVar 0 r) | (Set.member q $ colRet state) = call ctx ("cR" ++ show r)
astColVar state ctx (v@(ColVar l _)) | (l < level state) = astColVar (fromJust $ parent state) ctx v
astColVar state ctx c = CPPVar $ (colVarName c)

astLinearConstraint state ctx l o reif = 
  let (c,ll) = linearToListEx l
      in case (c,ll,o) of
        ((Const 0),[],_) -> CPPSimple $ CPPVar ("/* empty linear */")
        ((Const 0),[(i1,a),(i2,b)],_) | a==(-b) && a>0 -> CPPSimple $ CPPCall (CPPVar "rel") $ [ctx,astIntVar state ctx i1,astLinOperator o False,astIntVar state ctx i2] ++ astReifList state ctx reif
        ((Const 0),[(i2,a),(i1,b)],_) | a==(-b) && b>0 -> CPPSimple $ CPPCall (CPPVar "rel") $ [ctx,astIntVar state ctx i1,astLinOperator o False,astIntVar state ctx i2] ++ astReifList state ctx reif
        ((Const cc),[(i,(Const ff))],GOEqual) | (cc `mod` ff)==0 -> CPPSimple $ CPPCall (CPPVar "rel") $ [ctx,astIntVar state ctx i,CPPVar "IRT_EQ",astInt $ -cc `div` ff] ++ astReifList state ctx reif
        (c,[(i,Const 1)],rel) -> CPPSimple $ CPPCall (CPPVar "rel") $ [ctx,astIntVar state ctx i,astLinOperator o False,astIntExpr state ctx $ -c] ++ astReifList state ctx reif
        (c,[(i,Const (-1))],rel) -> CPPSimple $ CPPCall (CPPVar "rel") $ [ctx,astIntVar state ctx i,astLinOperator o True,astIntExpr state ctx $ c] ++ astReifList state ctx reif
        _ -> astTempList state (Just $ map snd ll) (Just $ map fst ll) Nothing ctx $ \ia iva _ -> [CPPSimple $ CPPCall (CPPVar "linear") $ [ctx,ia,iva,astLinOperator o False,astIntExpr state ctx $ -c] ++ astReifList state ctx reif]

astTempList :: CodegenGecodeState -> Maybe [GecodeIntConst] -> Maybe [IntVar] -> Maybe [BoolVar] -> CPPExpr -> (CPPExpr -> CPPExpr -> CPPExpr -> [CPPStat]) -> CPPStat
astTempList state i iv bv ctx f = CPPCompound $ 
  (
    (case i of Just ii -> [ CPPBlockDecl $ astDeclFn "ia" astTIA $ (astInt $ toInteger $ length ii) : [astIntExpr state ctx x | x <- ii] ]; _ -> []) ++ 
    (case iv of Just iiv -> [ CPPBlockDecl $ astDeclFn "iva" astTIVA $ [astInt $ toInteger $ length iiv] ] ++ [ CPPStatement $ CPPSimple $ CPPAssign (CPPIndex (CPPVar "iva") (astInt i)) CPPAssOp (astIntVar state ctx x) | (i,x) <- zip [0..] iiv ]; _ -> []) ++
    (case bv of Just ibv -> [ CPPBlockDecl $ astDeclFn "bva" astTBVA $ [astInt $ toInteger $ length ibv] ] ++ [ CPPStatement $ CPPSimple $ CPPAssign (CPPIndex (CPPVar "bva") (astInt i)) CPPAssOp (astBoolVar state ctx x) | (i,x) <- zip [0..] ibv ]; _ -> []) ++
    (map (CPPStatement) $ f (CPPVar "ia") (CPPVar "iva") (CPPVar "bva"))
  )

astTempSet state (num,fun) ctx f = CPPCompound $
  (
    [
      CPPBlockDecl $ astDeclFn "ia" astTIA [astIntExpr state ctx num],
      CPPStatement $ CPPFor (Right $ astDeclEq "asi" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "asi") CPPOpLe $ astIntExpr state ctx num) (Just $ CPPUnary CPPOpPostInc $ CPPVar "asi") $
        CPPSimple $ CPPAssign (CPPIndex (CPPVar "ia") (CPPVar "asi")) CPPAssOp (withPar (IntParDefCPP $ CPPVar "asi") state $ \state par -> astIntExpr state ctx $ fun (Term par)),
      CPPBlockDecl $ astDeclFn "is" (CPPTypePrim "IntSet") [CPPVar "ia"]
    ]
  ) ++ (map CPPStatement $ f $ CPPVar "is")

astTempSetConst state lst ctx f = CPPCompound $
  (
    [ CPPBlockDecl $ astDeclEqA "ia" (CPPArray [] astTInt $ Just $ astInt $ toInteger $ length lst) [astInt x | x <- lst],
      CPPBlockDecl $ astDeclFn "is" (CPPTypePrim "IntSet") [CPPVar "ia"]
    ]
  ) ++ (map CPPStatement $ f $ CPPVar "is")

astParTempList :: CodegenGecodeState -> GecodeListConst -> CPPExpr -> (CPPExpr -> [CPPStat]) -> CPPStat
astParTempList state (num,fun) ctx f = CPPCompound $
  (
    [
      CPPBlockDecl $ astDeclFn "ia" astTIA [astIntExpr state ctx num],
      CPPStatement $ CPPFor (Right $ astDeclEq "asi" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "asi") CPPOpLe $ astIntExpr state ctx num) (Just $ CPPUnary CPPOpPostInc $ CPPVar "asi") $
        CPPSimple $ CPPAssign (CPPIndex (CPPVar "ia") (CPPVar "asi")) CPPAssOp (withPar (IntParDefCPP $ CPPVar "asi") state $ \state par -> astIntExpr state ctx $ fun (Term par))
    ]
  ) ++ (map CPPStatement $ f $ CPPVar "ia")

astSection :: CodegenGecodeState -> GecodeColVarOrSection CodegenGecodeSolver -> CPPExpr -> (CPPExpr -> CPPExpr -> [CPPBlockItem]) -> CPPStat
astSection state (Left var) ctx f = CPPCompound $ f (astColVar state ctx var) (astColSize var state ctx)
astSection state (Right (var,(nn,ff))) ctx f = CPPCompound $
    [ CPPBlockDecl $ astDeclFn "as" astTIVA [astIntExpr state ctx nn],
      CPPStatement $ CPPFor (Right $ astDeclEq "asi" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "asi") CPPOpLe $ astIntExpr state ctx nn) (Just $ CPPUnary CPPOpPostInc $ CPPVar "asi") $
        CPPSimple $ CPPAssign (CPPIndex (CPPVar "as") (CPPVar "asi")) CPPAssOp (CPPIndex (astColVar state ctx var) (withPar (IntParDefCPP $ CPPVar "asi") state $ \state par -> astIntExpr state ctx $ ff (Term par)))
    ] ++ f (CPPVar "as") (astIntExpr state ctx nn)

astSectionM :: GecodeColVarOrSection CodegenGecodeSolver -> CPPExpr -> (CPPExpr -> CPPExpr -> CodegenGecodeSolver [CPPBlockItem]) -> CodegenGecodeSolver CPPStat
astSectionM (Left var) ctx m = do
  s <- get
  r <- m (astColVar s ctx var) (astColSize var s ctx)
  return $ CPPCompound r
astSectionM (Right (var,(nn,ff))) ctx f = do
  s <- get
  r <- f (CPPVar "as") (astIntExpr s ctx nn)
  return $ CPPCompound $
    [ CPPBlockDecl $ astDeclFn "as" astTIVA [astIntExpr s ctx nn],
      CPPStatement $ CPPFor (Right $ astDeclEq "asi" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "asi") CPPOpLe $ astIntExpr s ctx nn) (Just $ CPPUnary CPPOpPostInc $ CPPVar "asi") $
        CPPSimple $ CPPAssign (CPPIndex (CPPVar "as") (CPPVar "asi")) CPPAssOp (CPPIndex (astColVar s ctx var) (withPar (IntParDefCPP $ CPPVar "asi") s $ \state par -> astIntExpr state ctx $ ff (Term par)))
    ] ++ r

astMCPTypeName state = "MCPProgram"
astMCPType = CPPTypePrim . astMCPTypeName

withPar pardef state f =
  let l = length $ intPars state
      ss = state { intPars = (intPars state)++[pardef] }
      in f ss (GIParam l)

withParM pardef f = do
  s <- get
  let l = length $ intPars s
  put s { intPars = (intPars s)++[pardef] }
  r <- f (GIParam l)
  ss <- get
  put ss { intPars = intPars s }
  return r

astConstraint :: CPPExpr -> GecodeConstraint CodegenGecodeSolver -> CodegenGecodeSolver CPPStat
astConstraint ctx con = do
  procConstraint con
  state <- get
  let abv = astBoolVar state ctx
      aiv = astIntVar state ctx
      acv = astColVar state ctx
      tnm = "t" ++ (show $ level state)
      tnx i = "t" ++ (show $ level state) ++ [chr $ ord 'a' + i]
  ret <- case con of
    GCCond c b -> do
      inner <- astConstraint ctx c
      return $ CPPIf (astBoolExpr state ctx b) inner Nothing
    GCAll (GecodeIBFn f) (Left c) Nothing -> do
      inner <- astCompile $ f (IntVarCPP $ \ctx -> CPPIndex (astColVar state ctx c) (CPPVar tnm)) (BoolVarCPP $ \ctx -> CPPVar "/* GCAll undefined */")
      return $ CPPFor (Right $ astDeclEq tnm astTInt $ astInt 0 ) (Just $ CPPBinary (CPPVar tnm) CPPOpLe $ astColSize c state ctx) (Just $ CPPUnary CPPOpPostInc (CPPVar tnm)) inner
    GCAllC (GecodeCBFn f) (n,m) Nothing -> do
      inner <- withParM (IntParDefCPP $ CPPVar tnm) $ \par -> astCompile $ f (m $ Term par) (BoolVarCPP $ \ctx -> CPPVar "/* GCAllC undefined */")
      return $ CPPFor (Right $ astDeclEq tnm astTInt $ astInt 0) (Just $ CPPBinary (CPPVar tnm) CPPOpLe $ astIntExpr state ctx n) (Just $ CPPUnary CPPOpPostInc (CPPVar tnm)) inner
    GCAll (GecodeIBFn f) (Left c) (Just b) -> do
      inner <- astCompile $ f (IntVarCPP $ \ctx -> CPPIndex (astColVar state ctx c) (CPPVar (tnx 1))) (BoolVarCPP $ \ctx -> CPPIndex (CPPVar (tnx 0)) (CPPVar (tnx 1)))
      return $ CPPCompound $
        [
          CPPBlockDecl $ astDeclFn (tnx 0) (CPPTypePrim "BoolVarArray") [ctx,astColSize c state ctx,astInt 0,astInt 1],
          CPPStatement $ CPPFor (Right $ astDeclEq (tnx 1) astTInt $ astInt 0) (Just $ CPPBinary (CPPVar (tnx 1)) CPPOpLe $ astColSize c state ctx) (Just $ CPPUnary CPPOpPostInc (CPPVar (tnx 1))) inner,
          CPPStatement $ CPPSimple $ CPPCall (CPPVar "rel") [ctx,CPPVar "BOT_AND",CPPVar (tnx 0),abv b]
        ]
    GCAny (GecodeIBFn f) (Left c) (Just b) -> do
      inner <- astCompile $ f (IntVarCPP $ \ctx -> CPPIndex (astColVar state ctx c) (CPPVar $ tnx 1)) (BoolVarCPP $ \ctx -> CPPIndex (CPPVar $ tnx 0) (CPPVar $ tnx 1))
      return $ CPPCompound $
        [
          CPPBlockDecl $ astDeclFn (tnx 0) (CPPTypePrim "BoolVarArray") [ctx,astColSize c state ctx,astInt 0,astInt 1],
          CPPStatement $ CPPFor (Right $ astDeclEq (tnx 1) astTInt $ astInt 0) (Just $ CPPBinary (CPPVar $ tnx 1) CPPOpLe $ astColSize c state ctx) (Just $ CPPUnary CPPOpPostInc (CPPVar $ tnx 1)) inner,
          CPPStatement $ CPPSimple $ CPPCall (CPPVar "rel") [ctx,CPPVar "BOT_OR",CPPVar $ tnx 0,abv b]
        ]
    GCMap (GecodeIIFn f) (Left c) cr -> do
      inner <- astCompile $ f (IntVarCPP $ \ctx -> CPPIndex (astColVar state ctx c) (CPPVar tnm)) (IntVarCPP $ \ctx -> CPPIndex (astColVar state ctx cr) (CPPVar tnm))
      return $ CPPFor (Right $ astDeclEq tnm astTInt $ astInt 0) (Just $ CPPBinary (CPPVar tnm) CPPOpLe $ astColSize c state ctx) (Just $ CPPUnary CPPOpPostInc (CPPVar tnm)) inner
    GCFold (GecodeIIIFn f) c i res -> astSectionM c ctx $ \col siz -> do
      inner <- astCompile $ f (IntVarCPP $ \_ -> CPPVar (tnx 0)) (IntVarCPP $ \ctx -> CPPIndex col (CPPVar tnm)) (IntVarCPP $ \_ -> CPPVar (tnx 1))
      final <- astCompile $ f (IntVarCPP $ \_ -> CPPVar (tnx 0)) (IntVarCPP $ \ctx -> CPPIndex col (CPPBinary siz CPPOpSub 1)) res
      return $ [
          CPPBlockDecl $ astDeclEq (tnx 0) astTIV $ aiv i,
          CPPStatement $ CPPFor (Right $ astDeclEq tnm astTInt 0) (Just $ CPPBinary (CPPVar tnm) CPPOpLe $ CPPBinary siz CPPOpSub 1) (Just $ CPPUnary CPPOpPostInc (CPPVar tnm)) $ CPPCompound
            [
              CPPBlockDecl $ astDeclFn (tnx 1) astTIV [ctx,astLowerBound,astUpperBound],
              CPPStatement $ inner,
              CPPStatement $ CPPSimple $ CPPAssign (CPPVar (tnx 0)) CPPAssOp (CPPVar (tnx 1))
            ],
          CPPStatement $ final
        ]
    GCFoldC (GecodeICIFn f) (nnn) i res -> do
      inner <- withParM (IntParDefCPP $ CPPVar tnm) $ \par -> astCompile $ f (IntVarCPP $ \_ -> CPPVar (tnx 0)) (Term par) (IntVarCPP $ \_ -> CPPVar (tnx 1))
      final <- withParM (IntParDefCPP $ CPPBinary (astIntExpr state ctx nnn) CPPOpSub 1) $ \par -> astCompile $ f (IntVarCPP $ \_ -> CPPVar (tnx 0)) (Term par) res
      return $ CPPCompound
        [
          CPPBlockDecl $ astDeclEq (tnx 0) astTIV $ aiv i,
          CPPStatement $ CPPFor (Right $ astDeclEq tnm astTInt 0) (Just $ CPPBinary (CPPVar tnm) CPPOpLe $ CPPBinary (astIntExpr state ctx nnn) CPPOpSub 1) (Just $ CPPUnary CPPOpPostInc (CPPVar tnm)) $ CPPCompound
            [
              CPPBlockDecl $ astDeclFn (tnx 1) astTIV [ctx,astLowerBound,astUpperBound],
              CPPStatement $ inner,
              CPPStatement $ CPPSimple $ CPPAssign (CPPVar (tnx 0)) CPPAssOp (CPPVar (tnx 1))
            ],
          CPPStatement $ final
        ]
    _ -> return $ astSimpleConstraint ctx con state
--  return $ CPPCompound [ CPPStatement (CPPSimple $ CPPVar ("1 /* " ++(show con) ++ " */")), CPPStatement ret ]
  return ret

astSimpleConstraint ctx con state = case con of
  GCBoolVal bv val -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,abv bv,CPPVar "IRT_EQ",astBoolExpr state ctx val]
  GCBoolEqual b1 b2 -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,abv b1,CPPVar "IRT_EQ",abv b2]
  GCIntVal iv val -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,aiv iv,CPPVar "IRT_EQ",astIntExpr state ctx val]
  GCMult r a b -> CPPSimple $ CPPCall (CPPVar "mult") [ctx,aiv a,aiv b,aiv r]
  GCDiv r a b -> CPPSimple $ CPPCall (CPPVar "div") [ctx,aiv a,aiv b,aiv r]
  GCMod r a b -> CPPSimple $ CPPCall (CPPVar "mod") [ctx,aiv a,aiv b,aiv r]
  GCAbs r a -> CPPSimple $ CPPCall (CPPVar "abs") [ctx,aiv a,aiv r]
  GCAt (Left r)  (Left c)              (Left p)  -> CPPSimple $ CPPCall (CPPVar "element") [ctx,acv c,aiv p,aiv r]
  GCAt (Left r)  (Right (Left c))      (Left p)  -> astTempList state (Just $ map Const c) Nothing Nothing ctx $ \i _ _ -> [CPPSimple $ CPPCall (CPPVar "element") [ctx,i,aiv p,aiv r]]
  GCAt (Left r)  (Right (Right c))     (Left p)  -> astParTempList state c ctx $ \i -> [CPPSimple $ CPPCall (CPPVar "element") [ctx,i,aiv p,aiv r]]
  GCAt (Right r) (Left c)              (Left p)  -> CPPSimple $ CPPCall (CPPVar "element") [ctx,acv c,aiv p,astIntExpr state ctx r]
  GCAt (Right r) (Right (Left c))      (Left p)  -> astTempList state (Just $ map Const c) Nothing Nothing ctx $ \i _ _ -> [CPPSimple $ CPPCall (CPPVar "element") [ctx,i,aiv p,astIntExpr state ctx r]]
  GCAt (Right r) (Right (Right c))     (Left p)  -> astParTempList state c ctx $ \i -> [CPPSimple $ CPPCall (CPPVar "element") [ctx,i,aiv p,astIntExpr state ctx r]]
  GCAt (Left r)  (Left c)              (Right p) -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,CPPIndex (acv c) (astIntExpr state ctx p),CPPVar "IRT_EQ",aiv r]
  GCAt (Left r)  (Right (Left c))      (Right p) -> astTempList state (Just $ map Const c) Nothing Nothing ctx $ \i _ _ -> [CPPSimple $ CPPCall (CPPVar "element") [ctx,i,astIntExpr state ctx p,aiv r]]
  GCAt (Left r)  (Right (Right (n,f))) (Right p) -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,astIntExpr state ctx $ f p,CPPVar "IRT_EQ",aiv r]
  GCAt (Right r) (Left c)              (Right p) -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,CPPIndex (acv c) (astIntExpr state ctx p),CPPVar "IRT_EQ",astIntExpr state ctx r]
  GCAt (Right r) (Right (Left c))      (Right p) -> astTempList state (Just $ map Const c) Nothing Nothing ctx $ \i _ _ -> [CPPSimple $ CPPCall (CPPVar "element") [ctx,i,astIntExpr state ctx p,astIntExpr state ctx r]]
  GCAt (Right r) (Right (Right (n,f))) (Right p) -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,astIntExpr state ctx $ f p,CPPVar "IRT_EQ",astIntExpr state ctx r]
  GCDom v (Left c)          Nothing  -> CPPSimple $ CPPCall (CPPVar "count") [ctx,acv c,aiv v,CPPVar "IRT_GR",astInt 0]
  GCDom v (Right (Left c))  Nothing  -> astTempSetConst state c ctx $ \i -> [CPPSimple $ CPPCall (CPPVar "dom") [ctx,aiv v,i]]
  GCDom v (Right (Left c))  (Just b) -> astTempSetConst state c ctx $ \i -> [CPPSimple $ CPPCall (CPPVar "dom") [ctx,aiv v,i,abv b]]
  GCDom v (Right (Right c)) Nothing  -> astTempSet state c ctx      $ \i -> [CPPSimple $ CPPCall (CPPVar "dom") [ctx,aiv v,i]]
  GCDom v (Right (Right c)) (Just b) -> astTempSet state c ctx      $ \i -> [CPPSimple $ CPPCall (CPPVar "dom") [ctx,aiv v,i,abv b]]
  GCChannel a b -> CPPSimple $ CPPCall (CPPVar "channel") [ctx,aiv a,abv b]
  GCLinear l op ->       astLinearConstraint state ctx l op Nothing
  GCLinearReif l op b -> astLinearConstraint state ctx l op $ Just b
  -- TODO: Cat
  -- TODO: Take
  GCAnd lst r -> astTempList state Nothing Nothing (Just lst) ctx $ \_ _ b -> [CPPSimple $ CPPCall (CPPVar "rel") [ctx,CPPVar "BOT_AND",b,abv r]]
  GCOr lst r -> astTempList state Nothing Nothing (Just lst) ctx $ \_ _ b -> [CPPSimple $ CPPCall (CPPVar "rel") [ctx,CPPVar "BOT_OR",b,abv r]]
  GCNot r a -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,abv r,CPPVar "IRT_NQ",abv a]
  GCEquiv r a b -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,abv r,CPPVar "BOT_EQV",abv a,abv b]
  GCAllDiff b c -> astSection state c ctx $ \col siz -> [CPPStatement $ CPPSimple $ CPPCall (CPPVar "distinct") (if b then [ctx,col,CPPVar "ICL_DOM"] else [ctx,col])]
  GCSorted (Left c) op -> CPPSimple $ CPPCall (CPPVar "rel") [ctx,acv c,astLinOperator op False]
  GCSum c (Left i) -> astSection state c ctx $ \col siz -> [CPPStatement $ CPPSimple $ CPPCall (CPPVar "linear") [ctx,col,CPPVar "IRT_EQ",aiv i]]
  GCSum c (Right i) -> astSection state c ctx $ \col siz -> [CPPStatement $ CPPSimple $ CPPCall (CPPVar "linear") [ctx,col,CPPVar "IRT_EQ",astIntExpr state ctx i]]
  GCCount c (Left valvar) op (Left countvar) -> CPPSimple $ CPPCall (CPPVar "count") [ctx,astColVar state ctx c,astIntVar state ctx valvar,astLinOperator op False,astIntVar state ctx countvar]
  GCCount c (Right val) op (Left countvar) -> CPPSimple $ CPPCall (CPPVar "count") [ctx,astColVar state ctx c,astIntExpr state ctx val,astLinOperator op False,astIntVar state ctx countvar]
  GCCount c (Left valvar) op (Right count) -> CPPSimple $ CPPCall (CPPVar "count") [ctx,astColVar state ctx c,astIntVar state ctx valvar,astLinOperator op False,astIntExpr state ctx count]
  GCCount c (Right val) op (Right count) -> CPPSimple $ CPPCall (CPPVar "count") [ctx,astColVar state ctx c,astIntExpr state ctx val,astLinOperator op False,astIntExpr state ctx count]
  _ -> CPPSimple $ CPPVar $ "1 /*" ++ (show con) ++ "*/"
  where abv = astBoolVar state ctx
        aiv = astIntVar state ctx
        acv = astColVar state ctx
        tnm = "t" ++ (show $ level state)
        tnx i = "t" ++ (show $ level state) ++ [chr $ ord 'a' + i]

ifList :: Bool -> [a] -> [a]
ifList True x = x
ifList False _ = []

fnLoadColPar = 
  [
    "int nv=1;",
    "for (char *ptr=str; *ptr!=0; ptr++) {",
    "  nv += (*ptr == ',');",
    "}",
    "int *ret=new int[nv];",
    "for (int n=0; n<nv; n++) {",
    "  ret[n]=strtol(str,&str,10);",
    "  while (*str!=0 && *str!=',') str++;",
    "  str++;",
    "}",
    "*siz=nv;",
    "return ret;"
  ]

astTranslUnit = do
  pst <- astPost
  state <- get
  return $ CPPNamespace 
   [
    CPPElemDef $ CPPDef {
      cppDefName="loadCol",
      cppDefRetType=CPPPtr [] astTInt,
      cppDefStor=[],
      cppDefQual=[],
      cppDefArgs=[astDecl "str" $ CPPPtr [] (CPPTypePrim "char"),astDecl "siz" $ CPPPtr [] astTInt],
      cppDefBody=Just $ CPPVerbStat fnLoadColPar
    },
    CPPElemClass $ CPPClass {
      cppClassName = astMCPTypeName state,
      cppClassInherit = [(CPPPublic,CPPTypePrim "Space")],
      cppClassDecls = 
        (if nIntPars state > 0
           then [(CPPProtected,astDecl "iP" (CPPPtr [] astTInt))]
           else []
        ) ++
        (if nColPars state > 0
           then [(CPPProtected,astDecl "cP"  (CPPPtr [] $ CPPPtr [] astTInt)),
                 (CPPProtected,astDecl "cPs" (CPPPtr [] astTInt))
                ]
           else []
        ) ++
        ( map (\c -> (CPPPublic,astDecl (unvar $ astIntVar state astThis c) (CPPTypePrim "IntVar"))) $ Set.toList $ intRet state ) ++
        ( map (\c -> (CPPPublic,astDecl (unvar $ astColVar state astThis c) (CPPTypePrim "IntVarArray"))) $ Set.toList $ colRet state ) ++
        ( map (\c -> (CPPPublic,astDecl (unvar $ astBoolVar state astThis c) (CPPTypePrim "BoolVar"))) $ Set.toList $ boolRet state ),
      cppClassDefs = [
        (CPPPublic,CPPDef { 
           cppDefName="copy",
           cppDefRetType=CPPPtr [] (CPPTypePrim "Space"), 
           cppDefStor=[CPPVirtual], 
           cppDefQual=[],
           cppDefArgs=[astDecl "share" $ CPPTypePrim "bool"], 
           cppDefBody = Just $ CPPReturn $ Just $ CPPNew (astMCPType state) [CPPVar "share",astThis]
        }),
        (CPPPublic,CPPDef {
           cppDefName="print",
           cppDefRetType=CPPTypePrim "void",
           cppDefStor=[CPPVirtual],
           cppDefArgs=[astDecl "os" $ CPPRef [] $ CPPTypePrim "ostream"],
           cppDefQual=[CPPQualConst],
--           cppDefBody = Just $ CPPSimple $ case ret state of
--             Just r -> CPPBinary (CPPBinary (CPPVar "os") CPPOpShl (call astThis "ret")) CPPOpShl (CPPVar "endl")
--             _ -> CPPBinary (CPPBinary (CPPVar "os") CPPOpShl (CPPConst $ CPPConstString "Ok")) CPPOpShl (CPPVar "endl")
           cppDefBody = Just $ CPPReturn Nothing
        })
      ],
{-
        (
          case (minVar state) of
            Nothing -> []
            Just mv -> 
              [(CPPPublic,CPPDef {
                cppDefName="constrain",
                cppDefRetType=CPPTypePrim "void",
                cppDefStor=[],
                cppDefArgs=[astDecl "best_" $ CPPRef [CPPQualConst] (CPPTypePrim "Space")],
                cppDefQual=[],
                cppDefBody = Just $ CPPCompound $ 
                  [
                    CPPBlockDecl $ astDeclEq "best" (CPPPtr [] (CPPTypePrim "MCPProgram")) (CPPCast (CPPPtr [] (CPPTypePrim "MCPProgram")) (CPPUnary CPPOpAdr $ CPPVar "best_")),
                    CPPStatement $ CPPSimple $ CPPCall (CPPVar "rel") [astThis,CPPVar "cost",CPPVar "IRT_LE",CPPCall (CPPMember (CPPMember (CPPVar "best") "cost" True) "val" False) []]
                  ]
              })]
        ) -}
      cppClassConstrs = [
        (CPPPublic, CPPConstr { cppConstrStor=[], cppConstrArgs=
          (
            (if (nIntPars state)+(nColPars state) > 0
              then [astDecl "args" (CPPPtr [] $ CPPPtr [] $ CPPTypePrim "char")]
              else []
            )
          ), cppConstrBody = Just $ CPPCompound $ (
            (if (nIntPars state)+(nColPars state) > 0
              then [CPPStatement $ CPPSimple $ CPPUnary CPPOpPostInc (CPPVar "args")]
              else []
            ) ++
            (ifList (nIntPars state > 0) [CPPComment "init of iP", CPPStatement $ CPPVerbStat
              [
                "iP=new int["++(show (nIntPars state))++"];",
                "for (int i=0; i<"++(show (nIntPars state))++"; i++) {",
                "  iP[i]=strtol(*(args++),NULL,10);",
                "}"
              ]
            ])++
            (ifList (nColPars state > 0) [CPPComment "init of cP", CPPStatement $ CPPVerbStat
              [
                "cP=new int*["++(show (nColPars state))++"];",
                "cPs=new int["++(show (nColPars state))++"];",
                "for (int i=0; i<"++(show (nColPars state))++"; i++) {",
                "  cP[i]=loadCol(*(args++),cPs+i);",
                "}"
              ]
            ])++
{-            (case ret state of
              Nothing -> []
              Just r -> 
                [
                  CPPComment "init of ret",
                  CPPStatement $ CPPSimple $ CPPAssign (CPPVar "ret") CPPAssOp (CPPCall (CPPVar "IntVarArray") [astThis,astColSize r state astThis])
                ]
            ) ++  -}
            [CPPComment "begin of main post"]
          )++pst, cppConstrInit=[] 
{- (           [ (Left $ CPPVar $ boolVarName $ BoolVar (level state) j, [astThis,astInt 0,astInt 1]) | j <- Set.toList $ boolRet state ] ++
            [ (Left $ CPPVar $ intVarName $ IntVar (level state) j, [astThis,astLowerBound,astUpperBound]) | j <- Set.toList $ intRet state ] ++
            [ (Left $ CPPVar $ colVarName $ ColVar (level state) j, [astThis,astColSize (ColVar (level state) j) state astThis]) | j <- Set.toList $ colRet state ]

          ) -}
        }),
        (CPPPublic,CPPConstr { cppConstrStor=[], cppConstrArgs=[astDecl "share" $ CPPTypePrim "bool",astDecl "s" $ CPPRef [] $ astMCPType state], cppConstrInit=
          (
            [(Right (CPPTypePrim "Space"),[CPPVar "share",CPPVar "s"])] ++
            (if nIntPars state > 0
              then [(Left (CPPVar "iP"),[call (CPPVar "s") "iP"])]
              else []
            ) ++
            (if nColPars state > 0
              then [(Left (CPPVar "cP" ),[call (CPPVar "s") "cP" ]),
                    (Left (CPPVar "cPs"),[call (CPPVar "s") "cPs"])
                   ]
              else []
            )
          ), cppConstrBody = Just $ CPPCompound (
            [let vn = unvar $ astBoolVar state astThis j in CPPStatement $ CPPSimple $ CPPCall (call (call astThis vn) "update") [astThis,CPPVar "share",call (CPPVar "s") vn] | j <- Set.toList $ boolRet state] ++
            [let vn = unvar $ astIntVar state astThis j in CPPStatement $ CPPSimple $ CPPCall (call (call astThis vn) "update") [astThis,CPPVar "share",call (CPPVar "s") vn] | j <- Set.toList $ intRet state] ++
            [let vn = unvar $ astColVar state astThis j in CPPStatement $ CPPSimple $ CPPCall (call (call astThis vn) "update") [astThis,CPPVar "share",call (CPPVar "s") vn] | j <- Set.toList $ colRet state]
          )
        })
      ]
    }
   ]

astMainUnitGen = do
  state <- get
  return $ CPPNamespace 
    [ 
      CPPElemDef $ CPPDef {
        cppDefName="main",
        cppDefRetType=astTInt,
        cppDefStor=[],
        cppDefQual=[],
        cppDefArgs=[astDecl "argc" astTInt, astDecl "argv" $ CPPPtr [] $ CPPPtr [] $ CPPTypePrim "char"],
        cppDefBody=Just $ CPPCompound $
        ([
          CPPBlockDecl $ astDeclEq "prog" (CPPPtr [] $ astMCPType state) $ CPPNew (astMCPType state)
            (if ((nIntPars state)+(nColPars state) > 0)
              then [CPPVar "argv"]
              else []
            ),
          CPPStatement $ CPPSimple $ CPPCall (CPPVar "eval") [CPPVar "prog"],
          CPPStatement $ CPPReturn $ Just $ astInt 0
        ])
      }
    ]

astMainUnitDef = do
  state <- get
  return $ CPPNamespace
    [
      CPPElemDef $ CPPDef {
        cppDefName="main",
        cppDefRetType=astTInt,
        cppDefStor=[],
        cppDefQual=[],
        cppDefArgs=[astDecl "argc" astTInt, astDecl "argv" $ CPPPtr [] $ CPPPtr [] $ CPPTypePrim "char"],
        cppDefBody=Just $ CPPCompound $
        ([
          CPPBlockDecl $ astDeclEq "prog" (CPPPtr [] $ astMCPType state) $ CPPNew (astMCPType state)
            (if ((nIntPars state)+(nColPars state) > 0)
              then [CPPVar "argv"]
              else []
            ),
          CPPBlockDecl $ astDecl   "so"   (CPPTypePrim "Search::Options")
         ] ++ (if noTrailing $ options state then [
          CPPStatement $ CPPSimple $ CPPAssign (CPPMember (CPPVar "so") "c_d" False) CPPAssOp 1
         ] else []) ++ [
--          CPPBlockDecl $ astDeclFn "srch" (CPPTempl (case minVar state of { Nothing -> "DFS"; _ -> "BAB" }) [astMCPType state]) [CPPVar "prog",CPPVar "so"],
          CPPStatement $ CPPDelete $ CPPVar "prog",
          CPPStatement $ CPPWhile (astInt 0) True $ CPPCompound [
            CPPBlockDecl $ astDeclEq "sol" (CPPPtr [] $ astMCPType state) $ CPPCall (call (CPPVar "srch") "next") [],
            CPPStatement $ CPPIf (CPPUnary CPPOpNeg $ CPPVar "sol") CPPBreak Nothing,
            CPPStatement $ CPPSimple $ CPPCall (call (CPPUnary CPPOpInd $ CPPVar "sol") "print") [CPPVar "std::cout"]
          ],
          CPPStatement $ CPPReturn $ Just $ astInt 0
        ])
      }
    ]

astPost = do
  state <- get
  conss <- mapM (astConstraint astThis) (reverse $ cons state)
  state <- get
  return $
    [CPPComment "/* init col consts */"]++
    (concat [ case (colList state)!!pos of
      ColList lst -> [ CPPBlockDecl $ CPPDecl {
        cppDeclName=Just ("cte" ++ (show $ level state) ++ "_" ++ (show pos)),
        cppType=CPPArray [CPPQualConst] (CPPTypePrim "int") Nothing,
        cppTypeQual=[CPPQualConst],
        cppTypeStor=[],
        cppDeclInit=Just $ CPPInitArray [ astIntExpr state astThis x | x <- lst ]
       }]
      ColSlice f n p -> [ CPPBlockDecl $ CPPDecl {
        cppDeclName=Just ("cte" ++ (show $ level state) ++ "_" ++ (show pos)),
        cppType=CPPArray [] (CPPTypePrim "int") (Just $ astIntExpr state astThis n),
        cppTypeQual=[],
        cppTypeStor=[],
        cppDeclInit=Nothing
       },
       CPPStatement $  
         CPPFor 
           (Right $ astDeclEq "i" astTInt $ astInt 0)
           (Just $ CPPBinary (CPPVar "i") CPPOpLe $ astIntExpr state astThis n) 
           (Just $ CPPUnary CPPOpPostInc $ CPPVar "i") $ 
           CPPSimple $ CPPAssign 
             (CPPIndex (CPPVar ("cte" ++ (show $ level state) ++ "_" ++ (show pos))) $ CPPVar "i") 
             CPPAssOp $ 
             withPar (IntParDefCPP $ CPPVar "i") state $ \state par -> astColExpr state astThis p $ f $ Term par
       ]
      ColCat a b -> [ CPPBlockDecl $ CPPDecl {
        cppDeclName=Just ("cte" ++ (show $ level state) ++ "_" ++ (show pos)),
        cppType=CPPArray [] (CPPTypePrim "int") (Just $ astIntExpr state astThis $ size a + size b),
        cppTypeQual=[],
        cppTypeStor=[],
        cppDeclInit=Nothing
       },
       CPPStatement $
         CPPFor
           (Right $ astDeclEq "i" astTInt $ astInt 0)
           (Just $ CPPBinary (CPPVar "i") CPPOpLe $ astIntExpr state astThis $ size a)
           (Just $ CPPUnary CPPOpPostInc $ CPPVar "i") $
           CPPSimple $ CPPAssign
             (CPPIndex (CPPVar ("cte" ++ (show $ level state) ++ "_" ++ (show pos))) $ CPPVar "i")
             CPPAssOp $
             withPar (IntParDefCPP $ CPPVar "i") state $ \state par -> astColExpr state astThis a $ Term par,
       CPPStatement $
         CPPFor
           (Right $ astDeclEq "i" astTInt $ astIntExpr state astThis $ size a)
           (Just $ CPPBinary (CPPVar "i") CPPOpLe $ astIntExpr state astThis $ size a + size b)
           (Just $ CPPUnary CPPOpPostInc $ CPPVar "i") $
           CPPSimple $ CPPAssign
             (CPPIndex (CPPVar ("cte" ++ (show $ level state) ++ "_" ++ (show pos))) $ CPPVar "i")
             CPPAssOp $
             withPar (IntParDefCPP $ CPPVar "i") state $ \state par -> astColExpr state astThis b $ (Term par) - (size a)
       ]
      x -> error $ "Unsupported operation on constant lists: " ++ (show x)
     | pos <- [0..(length (colList state))-1] 
    ]) ++
    (
        [CPPComment "decl boolvars"]++[
          let glob = (Set.member (BoolVar 0 j) (boolRet state) && level state == 0) 
              in (if glob then (\x -> CPPStatement $ CPPSimple $ CPPAssign (astBoolVar state astThis $ BoolVar (level state) j) CPPAssOp $ CPPCall (CPPVar "BoolVar") x )else (\x -> CPPBlockDecl $ astDeclFn ((\(CPPVar x) -> x) $ astBoolVar state astThis (BoolVar (level state) j)) astTBV x)) [astThis,astInt 0,astInt 1] | j <- [0..nBoolVars state - 1]
        ]
    ) ++
    (
        [CPPComment "decl intvars"]++[
          let glob = (Set.member (IntVar 0 j) (intRet state) && level state == 0) 
              in (if glob then (\x -> CPPStatement $ CPPSimple $ CPPAssign (astIntVar state astThis $ IntVar (level state) j) CPPAssOp $ CPPCall (CPPVar "IntVar") x )else (\x -> CPPBlockDecl $ astDeclFn ((\(CPPVar x) -> x) $ astIntVar state astThis (IntVar (level state) j)) astTIV x)) [astThis,astLowerBound,astUpperBound] | j <- [0..nIntVars state - 1]
        ]
    ) ++
    ( 
        [CPPComment "decl colvars"]++[
          let glob = (Set.member (ColVar 0 j) (colRet state) && level state == 0) 
              in (if glob then (\x -> CPPStatement $ CPPSimple $ CPPAssign (astColVar state astThis $ ColVar (level state) j) CPPAssOp $ CPPCall (CPPVar "IntVarArray") x ) else (\x -> CPPBlockDecl $ astDeclFn ((\(CPPVar x) -> x) $ astColVar state astThis (ColVar (level state) j)) astTIVA x)) ((if glob then (astThis:) else id) [astColSize (ColVar (level state) j) state astThis]) | j <- [0..length (colVars state) - 1]
        ]
    ) ++
    [CPPComment $ "init col vars"]++
    [ CPPStatement $ case x of
        ColDefSize s -> CPPCompound [CPPComment "ColDefSize",CPPStatement $ CPPFor (Right $ astDeclEq "i" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "i") CPPOpLe $ astIntExpr state astThis s) (Just $ CPPUnary CPPOpPostInc (CPPVar "i")) $
          CPPSimple $ CPPCall (call (CPPIndex (astColVar state astThis i) (CPPVar "i")) "init") [astThis,astLowerBound,astUpperBound]
         ]
        ColDefList l -> CPPCompound $ 
            (CPPComment "ColDefList") :
            [ CPPStatement $ CPPSimple $ CPPAssign (CPPIndex (astColVar state astThis i) (astInt $ toInteger i2)) CPPAssOp $ (astIntVar state astThis f2) | (i2,f2) <- zip [0..(length l)-1] l ]
        ColDefCat a b -> CPPCompound $ [
              CPPComment "ColDefCat",
              CPPStatement $ CPPFor (Right $ astDeclEq "i" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "i") CPPOpLe $ astColSize a state astThis) (Just $ CPPUnary CPPOpPostInc (CPPVar "i")) $ CPPSimple $ CPPAssign (CPPIndex (astColVar state astThis i) (CPPVar "i")) CPPAssOp (CPPIndex (astColVar state astThis a) (CPPVar "i")),
              CPPStatement $ CPPFor (Right $ astDeclEq "i" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "i") CPPOpLe $ astColSize b state astThis) (Just $ CPPUnary CPPOpPostInc (CPPVar "i")) $ CPPSimple $ CPPAssign (CPPIndex (astColVar state astThis i) (CPPVar "i" + astColSize a state astThis)) CPPAssOp (CPPIndex (astColVar state astThis b) (CPPVar "i"))
            ]
  {-      ColDefTake a p l -> CPPCompound $ [
            CPPBlockDecl $ astDeclFn "b" astTIVA [astThis,astIntExpr state astThis l],
            CPPStatement $ CPPFor (Right $ astDeclEq "i" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "i") CPPOpLe $ astColSize a state astThis) (Just $ CPPUnary CPPOpPostInc (CPPVar "i")) $ CPPSimple $ CPPAssign (CPPIndex (CPPVar "b") (CPPVar "i")) CPPAssOp (CPPIndex (astColVar state astThis a) (CPPVar "i" + (astIntExpr state astThis p))),
            CPPStatement $ CPPSimple $ CPPAssign (astColVar state astThis i) CPPAssOp (CPPVar "b")
          ]-}
      | (i,x) <- zip (map (ColVar (level state)) [0..(length $ colVars state)-1]) $ colVars state ] ++
{-     (case (ret state) of
       Nothing -> []
       Just (ColVar 0 _) | level state == 0 -> []
       Just r -> 
         [
           CPPComment "init ret",
           CPPStatement $ CPPFor (Right $ astDeclEq "i" astTInt $ astInt 0) (Just $ CPPBinary (CPPVar "i") CPPOpLe $ astColSize r state astThis) (Just $ CPPUnary CPPOpPostInc (CPPVar "i")) $ CPPSimple $ CPPAssign (CPPIndex (call astThis "ret") (CPPVar "i")) CPPAssOp (CPPIndex (astColVar state astThis r) (CPPVar "i"))
         ]
     ) ++ -}
     [CPPComment "constraints"]++[ CPPStatement x | x <- conss ] ++
     (if level state == 0
       then 
         [CPPComment "branchers" ]
{-         (case minVar state of
           Nothing -> []
           Just m -> 
             [
               CPPStatement $ CPPSimple $ CPPAssign (CPPVar "cost") CPPAssOp (astIntVar state astThis m),
               CPPStatement $ CPPSimple $ CPPCall (CPPVar "branch") [astThis,call astThis "cost",CPPVar "INT_VAL_MIN"]
             ]
         )++ -}
--         ([CPPStatement $ CPPSimple $ CPPCall (CPPVar "branch") [astThis,call astThis "ret",CPPVar "INT_VAR_SIZE_MIN",CPPVar "INT_VAL_SPLIT_MIN"]])
       else  []
     )

transExprV (Term DDomSize) = domsizeV
transExprV (Term DMedian) = medianD

transExprC (Rel (Term VarRef) ERLess (Term ValRef)) = ($<)
transExprC (Rel (Term VarRef) ERLess (Plus (Const 1) (Term ValRef))) = ($<=)
transExprC (Rel (Term ValRef) ERLess (Term VarRef)) = ($>)
transExprC (Rel (Plus (Const 1) (Term ValRef)) ERLess (Term VarRef)) = ($>=)
transExprC (Rel (Term VarRef) EREqual (Term ValRef)) = ($==)
transExprC (Rel (Term ValRef) EREqual (Term VarRef)) = ($==)
transExprC x = error $ "transExprC doesn't support " ++ show x

transDir Maximize = maxV
transDir Minimize = minV

transSearch state (Labelling (LabelInt v x f)) = Base.vlabel (unvar $ astIntVar state astThis v) (transExprV x) (transExprC $ f (Term VarRef) (Term ValRef))
transSearch state (Labelling (LabelCol a x o d f)) = Base.label (unvar $ astColVar state astThis a) (transExprV x) (transDir o) (transExprV d) (transExprC $ f (Term VarRef) (Term ValRef))
transSearch state (CombineSeq a b) = transSearch state a <&> transSearch state b
transSearch state (CombinePar a b) = transSearch state a <|> transSearch state b
transSearch state (TryOnce a) = once <@> transSearch state a
transSearch state (LimitSolCount 1 a) = once <@> transSearch state a
transSearch state (PrintSol _ v _ a) = prt (map (unvar . astColVar state astThis) v) <@> transSearch state a
transSearch state (BranchBound v Minimize a) = bbmin (unvar $ astIntVar state astThis v) <@> transSearch state a

generateGecode :: CompilableModel t => t -> String
generateGecode x = 
  let ([tru,mnu],state) = run $ compile False x $ retState astGenerate
      sru = case (noGenSearch $ options state) of
        True -> ""
        False -> search $ transSearch state $ fromJust $ searchSpec state
{-      sru = case (noGenSearch $ options state) of
        True -> ""
        False -> case (minVar state) of
          Nothing -> search $ prt ["branch"] <@> fs <@> Generator.label "branch" domsizeV minV medianD ($<=)
          Just _ -> search $ prt ["branch"] <@> (bbmin "cost" <@> (Generator.label "bound" lbV minV medianD ($==) <&> Generator.label "branch" domsizeV minV medianD ($<=) {- <&> Generator.label "bound" lbV minV meanD ($==) -} ))
-}
      ret = codegen tru ++ sru ++ codegen mnu
      in ret
