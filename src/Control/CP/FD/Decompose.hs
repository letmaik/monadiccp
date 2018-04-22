{- 
 -      Monadic Constraint Programming
 -      http://www.cs.kuleuven.be/~toms/MCP/
 -      Pieter Wuille
 -}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DatatypeContexts #-}

module Control.CP.FD.Decompose (
  DecompData,
  baseDecompData,
  decompose,
  decomposeEx,
  decompBoolLookup,
  decompIntLookup,
  decompColLookup,
) where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Lazy hiding (state)

import Control.CP.Debug
import Data.Expr.Data
import Data.Expr.Util
import Control.CP.FD.Graph
import Control.CP.FD.Model

data DecompData = DecompData {
  -- expressions currently accessible as variables
  cseMapBool :: Map ModelBool EGVarId,
  cseMapInt :: Map ModelInt EGVarId,
  cseMapCol :: Map ModelCol EGVarId,
  -- parent graph's data
  cseParent :: Maybe DecompData,
  -- expressions imported from parent graph
  cseImports :: ([ModelBool],[ModelInt],[ModelCol]),
  -- counter for unique id's
  cseNIds :: Int,
  -- locked nodes (already shown to the caller, and cannot be unified/replaced anymore)
  cseLocked :: EGTypeData (Set EGVarId),
  -- level of nesting
  cseLevel :: Int
}

decompBoolLookup :: DecompData -> ModelBool -> Maybe EGVarId
decompBoolLookup d v = Map.lookup v $ cseMapBool d

decompIntLookup :: DecompData -> ModelInt -> Maybe EGVarId
decompIntLookup d v = Map.lookup v $ cseMapInt d

decompColLookup :: DecompData -> ModelCol -> Maybe EGVarId
decompColLookup d v = Map.lookup v $ cseMapCol d

-- | base instance of DecompData
baseDecompData :: DecompData
baseDecompData = DecompData {
  cseMapBool = Map.empty,
  cseMapInt = Map.empty,
  cseMapCol = Map.empty,
  cseParent = Nothing,
  cseImports = ([],[],[]),
  cseNIds = 0,
  cseLevel = 0,
  cseLocked = baseTypeData (Set.empty)
}

-- | the state for the DCMonad
data DCState = DCState {
  dcsData :: DecompData,
  dcsModel :: EGModel
}

-- | base state for the DCMonad
baseDCState = DCState {
  dcsData = baseDecompData,
  dcsModel = baseGraph
}

-- | definition of a decomposer monad
newtype DCMonad a = DCMonad { state :: State DCState a }
  deriving (Monad, Applicative, Functor, MonadState DCState)

-- | transform an expression into a graph, taking and returning an updated state
decomposeEx :: DecompData -> Int -> Model -> ([ModelBool],[ModelInt],[ModelCol]) -> Maybe EGModel -> (DecompData,EGModel,Int)
decomposeEx dat vars model (lb,li,lc) prev = 
  let prog = do
        s1 <- get
        put $ s1 { dcsData = (dcsData s1) { cseNIds = max vars (cseNIds $ dcsData s1) } }
        decomposeBoolEx (Just True) model
        mapM_ decomposeBool lb
        mapM_ decomposeInt li
        mapM_ decomposeCol lc
        s2 <- get
        put $ s2 { dcsData = (dcsData s2) { cseLocked = egTypeDataMap (\f -> Set.fromList $ Map.keys $ f $ egmLinks $ dcsModel s2) } }
      pmodel = case prev of
        Nothing -> baseGraph
        Just x -> x
      res = execState (state prog) $ DCState { dcsData = dat, dcsModel = pmodel }
      in (dcsData res,dcsModel res,cseNIds $ dcsData res)

-- | easier version of decomposeEx that does not require or return a state
decompose :: Model -> EGModel
decompose x = (\(_,x,_) -> x) $ decomposeEx baseDecompData 0 x ([],[],[]) Nothing

-- | decomposition states can be stacked, this function tests whether a property hold
-- for a state or any of its parents
stateProperty :: (DecompData -> Bool) -> DecompData -> Bool
stateProperty f s = if f s then True else case (cseParent s) of
  Just p -> stateProperty f p
  _ -> False

newVar :: EGVarType -> DCMonad EGVarId
newVar typ = do
  s <- get
  let (nv,nm) = addNode typ (dcsModel s)
  put $ s { dcsModel = nm }
  return nv

importBool :: Maybe Bool -> ModelBool -> DCMonad EGVarId
importBool val expr = do
  n <- newBoolVar val expr
  s <- get
  if cseLevel (dcsData s) == 0
    then error $ "Boolean expression (value="++(show val)++") escapes: " ++ (show expr)
    else do
      let ni = length $ (\(x,_,_)->x) $ cseImports $ dcsData s
      put $ s { dcsData = (dcsData s) { cseImports = (\(a,b,c) -> (a++[expr],b,c)) (cseImports $ dcsData s) } }
      addConstraint (EGBoolExtern ni) ([n],[],[])
      return n

importInt :: ModelInt -> DCMonad EGVarId
importInt expr = do
  n <- newIntVar expr
  s <- get
  if cseLevel (dcsData s) == 0
    then error $ "Integer expression escapes: " ++ (show expr)
    else do
      let ni = length $ (\(_,x,_)->x) $ cseImports $ dcsData s
      put $ s { dcsData = (dcsData s) { cseImports = (\(a,b,c) -> (a,b++[expr],c)) (cseImports $ dcsData s) } }
      addConstraint (EGIntExtern ni) ([],[n],[])
      return n

importCol :: ModelCol -> DCMonad EGVarId
importCol expr = do
  n <- newColVar expr
  s <- get
  if cseLevel (dcsData s) == 0
    then error $ "Collection expression escapes: " ++ (show expr)
    else do
      let ni = length $ (\(_,_,x)->x) $ cseImports $ dcsData s
      put $ s { dcsData = (dcsData s) { cseImports = (\(a,b,c) -> (a,b,c++[expr])) (cseImports $ dcsData s) } }
      addConstraint (EGColExtern ni) ([],[],[n])
      return n

unifyVars :: EGVarType -> EGVarId -> EGVarId -> DCMonad Bool
unifyVars typ v1 v2 = do
  s <- get
  let rm = egTypeGet typ $ cseLocked $ dcsData s
      i1 = Set.member v1 rm
      i2 = Set.member v2 rm
  if (i1 && i2)
    then return False  -- if both nodes are locked, unification is not possible
    else if i1
      then unifyVars typ v2 v1 -- if only i1 is locked, unify v2 with v1 instead of v1 with v2
      else do -- otherwise, really unify
        let nm = unifyNodes typ v1 v2 (dcsModel s)
        case typ of
          EGBoolType -> put $ s { dcsModel = nm, dcsData = (dcsData s) { cseMapBool = Map.map tran $ cseMapBool $ dcsData s } }
          EGIntType  -> put $ s { dcsModel = nm, dcsData = (dcsData s) { cseMapInt = Map.map tran $ cseMapInt $ dcsData s } }
          EGColType  -> put $ s { dcsModel = nm, dcsData = (dcsData s) { cseMapCol = Map.map tran $ cseMapCol $ dcsData s } }
        return True
  where tran = unifyIds v1 v2

addConstraint :: EGConstraintSpec -> ([EGVarId],[EGVarId],[EGVarId]) -> DCMonad ()
addConstraint spec (lb,li,lc) = do
  s <- get
  let nm = addEdge spec (EGTypeData { boolData=lb, intData=li, colData=lc }) (dcsModel s)
  put $ s { dcsModel = nm }

newBoolVar :: Maybe Bool -> ModelBool -> DCMonad EGVarId
newBoolVar val expr = do
  n <- case val of
    Nothing -> newVar EGBoolType
    Just x -> decomposeBool $ BoolConst x
  s <- get
  let nc = Map.insert expr n (cseMapBool $ dcsData s)
  put $ s { dcsData = (dcsData s) { cseMapBool = nc } }
  return n

newIntVar :: ModelInt -> DCMonad EGVarId
newIntVar expr = do
  n <- newVar EGIntType
  s <- get
  let nc = Map.insert expr n (cseMapInt $ dcsData s)
  put $ s { dcsData = (dcsData s) { cseMapInt = nc } }
  return n

newColVar :: ModelCol -> DCMonad EGVarId
newColVar expr = do
  n <- newVar EGColType
  s <- get
  let nc = Map.insert expr n (cseMapCol $ dcsData s)
  put $ s { dcsData = (dcsData s) { cseMapCol = nc } }
  return n

decomposeSubmodel :: (Int,Int,Int) -> (([ModelBool],[ModelInt],[ModelCol]) -> DCMonad ()) -> DCMonad (EGModel,([EGVarId],[EGVarId],[EGVarId]))
decomposeSubmodel (nArgsBool,nArgsInt,nArgsCol) m = do
  oArgsBool <- mapM (const $ nextId >>= (\x -> return $ BoolTerm $ ModelBoolVar $ x)) [1..nArgsBool]
  oArgsInt  <- mapM (const $ nextId >>= (\x -> return $ Term     $ ModelIntVar  $ x)) [1..nArgsInt]
  oArgsCol  <- mapM (const $ nextId >>= (\x -> return $ ColTerm  $ ModelColVar  $ x)) [1..nArgsCol]
  s <- get
  let sm = m (oArgsBool,oArgsInt,oArgsCol)
      ns = execState (state sm) $ baseDCState { dcsData = (dcsData baseDCState) { cseLevel = 1 + (cseLevel $ dcsData s), cseNIds = 0+(cseNIds $ dcsData s), cseParent = Just $ dcsData s } }
  put $ s { dcsData = (dcsData s) { cseNIds = 0+(cseNIds $ dcsData ns) } }
  argsBool <- mapM decomposeBool $ (\(x,_,_) -> x) $ cseImports $ dcsData ns
  argsInt <-  mapM decomposeInt  $ (\(_,x,_) -> x) $ cseImports $ dcsData ns
  argsCol <-  mapM decomposeCol  $ (\(_,_,x) -> x) $ cseImports $ dcsData ns
  return (dcsModel ns, (argsBool,argsInt,argsCol))

constIntTrans :: ModelIntTerm ModelFunctions -> EGParTerm
constIntTrans (ModelIntPar x) = EGPTParam x
constIntTrans x = error $ "non-constant int transform: "++(show x)
constColTrans :: ModelColTerm ModelFunctions -> EGParColTerm
constColTrans (ModelColPar x) = EGPTColParam x
constColTrans x = error $ "non-constant col transform: "++(show x)
constBoolTrans :: ModelBoolTerm ModelFunctions -> EGParBoolTerm
constBoolTrans (ModelBoolPar x) = EGPTBoolParam x
constBoolTrans x = error $ "non-constant bool transform: "++(show x)
constIntTransInv :: EGParTerm -> ModelIntTerm ModelFunctions
constIntTransInv (EGPTParam x) = ModelIntPar x
constColTransInv :: EGParColTerm -> ModelColTerm ModelFunctions
constColTransInv (EGPTColParam x) = ModelColPar x
constBoolTransInv :: EGParBoolTerm -> ModelBoolTerm ModelFunctions
constBoolTransInv (EGPTBoolParam x) = ModelBoolPar x

constTrans = (constIntTrans,constColTrans,constBoolTrans,constIntTransInv,constColTransInv,constBoolTransInv)
invConstTrans = (constIntTransInv,constColTransInv,constBoolTransInv,constIntTrans,constColTrans,constBoolTrans)

dependenceTester d = 
  (
    \x -> if Map.member x (cseMapInt d) && not (x `elem` ((\(_,x,_) -> x) $ cseImports d)) then Just True else Nothing,
    \x -> if Map.member x (cseMapCol d) && not (x `elem` ((\(_,_,x) -> x) $ cseImports d)) then Just True else Nothing,
    \x -> case x of
      BoolTerm (ModelExtra _) -> Just True
      _ -> if Map.member x (cseMapBool d) && not (x `elem` ((\(x,_,_) -> x) $ cseImports d)) then Just True else Nothing
  )

dependentIntExpr :: DecompData -> ModelInt -> Bool
dependentIntExpr d = propertyEx $ dependenceTester d
dependentBoolExpr :: DecompData -> ModelBool -> Bool
dependentBoolExpr d = boolPropertyEx $ dependenceTester d
dependentColExpr :: DecompData -> ModelCol -> Bool
dependentColExpr d = colPropertyEx $ dependenceTester d

nextId :: DCMonad Int
nextId = do
  s <- get
  let n = cseNIds $ dcsData s
  put $ s { dcsData = (dcsData s) { cseNIds = n + 1 } }
  return n

-----------------------------------------
-- | Decomposition of special values | --
-----------------------------------------

decomposeBool :: ModelBool -> DCMonad EGVarId
decomposeBool expr = do
  (Just x) <- decomposeBoolEx Nothing expr
  return x

decomposeBoolEx :: Maybe Bool -> ModelBool -> DCMonad (Maybe EGVarId)
decomposeBoolEx val expr = do
  s <- get
  debug ("decomposeBoolEx [level "++(show $ cseLevel $ dcsData s)++"] val="++(show val)++" expr="++(show expr)) $ return ()
  let key = expr
  case Map.lookup key (cseMapBool $ dcsData s) of    -- local variable or already locally decomposed expression
    Just i -> do
      debug ("decomposeBoolEx [level "++(show $ cseLevel $ dcsData s)++"] val="++(show val)++" expr="++(show expr)++": already decomposed: "++(show i)) $ return ()
      return $ Just i
    Nothing -> if (modelVariantBool expr)
      then do
        if (stateProperty (Map.member key . cseMapBool) $ dcsData s) && not (dependentBoolExpr (dcsData s) expr) && (cseLevel $ dcsData s) > 0
          then do   -- Loop Invariant Code Motion
            debug ("decomposeBoolEx: [level "++(show $ cseLevel $ dcsData s)++"] [variant indep] "++(show expr)) $ return ()
            n <- importBool val expr
            return $ Just n
          else do
            debug ("decomposeBoolEx: [level "++(show $ cseLevel $ dcsData s)++"] [variant dep] "++(show expr)) $ return ()
            realDecomposeBoolEx val expr
        else do
          debug ("decomposeBoolEx: [level "++(show $ cseLevel $ dcsData s)++"] [invariant] "++(show expr)) $ return ()
          n <- newBoolVar val expr
          let tr = boolTransform constTrans expr
          addConstraint (EGBoolValue tr) ([n],[],[])
          return $ Just n

decomposeInt :: ModelInt -> DCMonad EGVarId
decomposeInt expr = do
  s <- get
  debug ("decomposeInt [level "++(show $ cseLevel $ dcsData s)++"] expr="++(show expr)) $ return ()
  let key = expr
  case Map.lookup key (cseMapInt $ dcsData s) of
    Just i -> return i
    Nothing -> if (modelVariantInt expr)
      then if (stateProperty (Map.member key . cseMapInt) $ dcsData s) && not (dependentIntExpr (dcsData s) expr) && (cseLevel $ dcsData s) > 0
        then do
          debug ("decomposeInt: [level "++(show $ cseLevel $ dcsData s)++"] [variant indep] "++(show expr)) $ return ()
          importInt expr
        else do
          debug ("decomposeInt: [level "++(show $ cseLevel $ dcsData s)++"] [variant dep] "++(show expr)) $ return ()
          realDecomposeInt expr
      else do
        debug ("decomposeInt: [level "++(show $ cseLevel $ dcsData s)++"] [invariant] "++(show expr)) $ return ()
        n <- newIntVar expr
        let tr = transform constTrans expr
        addConstraint (EGIntValue tr) ([],[n],[])
        return n

decomposeCol :: ModelCol -> DCMonad EGVarId
decomposeCol expr = do
  s <- get
  debug ("decomposeCol [level "++(show $ cseLevel $ dcsData s)++"] expr="++(show expr)) $ return ()
  let key = expr
  case Map.lookup key (cseMapCol $ dcsData s) of
    Just i -> return i
    Nothing -> if (modelVariantCol expr)
      then if (stateProperty (Map.member key . cseMapCol) $ dcsData s) && not (dependentColExpr (dcsData s) expr) && (cseLevel $ dcsData s) > 0
        then do
          debug ("decomposeCol: [level "++(show $ cseLevel $ dcsData s)++"] [variant indep] "++(show expr)) $ return ()
          importCol expr
        else do 
          debug ("decomposeCol: [level "++(show $ cseLevel $ dcsData s)++"] [variant dep] "++(show expr)) $ return ()
          realDecomposeCol expr
      else do
        debug ("decomposeCol: [level "++(show $ cseLevel $ dcsData s)++"] [invariant] "++(show expr)) $ return ()
        n <- newColVar expr
        let tr = colTransform constTrans expr
        addConstraint (EGColValue tr) ([],[],[n])
        return n


------------------------------------------
-- | Real decomposers for expressions | --
------------------------------------------

realDecomposeBoolEx :: Maybe Bool -> ModelBool -> DCMonad (Maybe EGVarId)
realDecomposeBoolEx val expr = case expr of
  BoolTerm (ModelExtra (ForNewBool f)) -> do
    n <- nextId
    let v = BoolTerm $ ModelBoolVar n
    newBoolVar Nothing v
    decomposeBoolEx val $ f v
  BoolTerm (ModelExtra (ForNewInt f)) -> do
    n <- nextId
    let v = Term $ ModelIntVar n
    newIntVar v
    decomposeBoolEx val $ f v
  BoolTerm (ModelExtra (ForNewCol f)) -> do
    n <- nextId
    let v = ColTerm $ ModelColVar n
    newColVar v
    decomposeBoolEx val $ f v
  BoolTerm (ModelBoolVar i) -> do
    n <- newBoolVar val expr
    return $ Just n
  BoolCond c t f -> case val of
    Just True -> do
      dc <- decomposeBool c
      di <- decomposeBool $ boolSimplify $ BoolNot c
      ct <- decomposeBool (BoolConst True)
      if (t /= BoolConst True) 
        then do
          dt <- decomposeBool t
          addConstraint EGCondEqual ([dc,dt,ct],[],[])
        else return ()
      if (f /= BoolConst True)
        then do
          df <- decomposeBool f
          addConstraint EGCondEqual ([di,df,ct],[],[])
        else return ()
      return Nothing
    _ -> error "No reified boolean conditional exists"
  BoolAnd a b -> case val of
    Just True -> do
      decomposeBoolEx val a
      decomposeBoolEx val b
      return Nothing
    _ -> do
      n <- newBoolVar val expr
      ad <- decomposeBool a
      bd <- decomposeBool b
      addConstraint EGAnd ([n,ad,bd],[],[])
      return $ Just n
  BoolOr a b -> case val of
    Just False -> do
      decomposeBoolEx val a
      decomposeBoolEx val b
      return Nothing
    _ -> do
      n <- newBoolVar val expr
      ad <- decomposeBool a
      bd <- decomposeBool b
      addConstraint EGOr ([n,ad,bd],[],[])
      return $ Just n
  BoolNot a -> case val of
    Just True -> do
      decomposeBoolEx (Just False) a
      return Nothing
    Just False -> do
      decomposeBoolEx (Just True) a
      return Nothing
    _ -> do
      n <- newBoolVar val expr
      ad <- decomposeBool a
      addConstraint EGNot ([n,ad],[],[])
      return $ Just n
  Rel a r b -> case (r,val) of
    (EREqual,Just True) -> do
      ad <- decomposeInt a
      bd <- decomposeInt b
      res <- unifyVars EGIntType ad bd
      if res
        then return Nothing
        else do
          n <- decomposeBool (BoolConst True)
          addConstraint EGEqual ([n],[ad,bd],[])
          return Nothing
    (ERDiff,Just False) -> do
      ad <- decomposeInt a 
      bd <- decomposeInt b
      res <- unifyVars EGIntType ad bd
      if res
        then return Nothing
        else do
          n <- decomposeBool (BoolConst True)
          addConstraint EGEqual ([n],[ad,bd],[])
          return Nothing
    _ -> do
      n <- newBoolVar val expr
      ad <- decomposeInt a
      bd <- decomposeInt b
      addConstraint (case r of
          EREqual -> EGEqual
          ERDiff -> EGDiff
          ERLess -> EGLess True
        ) ([n],[ad,bd],[])
      return $ Just n
  ColEqual a b -> case val of
    Just True -> do
      ad <- decomposeCol a
      bd <- decomposeCol b
      res <- unifyVars EGColType ad bd
      if not res
        then error "unification of collections failed"
        else return Nothing
    _ -> error "No negated or reified version of ColEqual exists"
  AllDiff b c -> case val of
    Just True -> do
      ac <- decomposeCol c
      addConstraint (EGAllDiff b) ([],[],[ac])
      return Nothing
    _ -> error "No negated or reified version of AllDiff exists"
  Sorted b c -> case val of
    Just True -> do
      ac <- decomposeCol c
      addConstraint (EGSorted b) ([],[],[ac])
      return Nothing
    _ -> error "No negated or reified version of Sorted exists"
  Dom i c -> case val of
    Just True -> do
      ac <- decomposeCol c
      ai <- decomposeInt i
      addConstraint EGDom ([],[ai],[ac])
      return Nothing
    _ -> error "No negated or reified version of Dom exists"
  BoolEqual a b -> case val of
    Just True -> do
      ad <- decomposeBool a
      bd <- decomposeBool b
      res <- unifyVars EGBoolType ad bd
      if res
        then return Nothing
        else do
          n <- decomposeBool (BoolConst True)
          addConstraint EGEquiv ([n,ad,bd],[],[])
          return Nothing
    _ -> do
      n <- newBoolVar val expr
      ad <- decomposeBool a
      bd <- decomposeBool b
      addConstraint EGEquiv ([n,ad,bd],[],[])
      return $ Just n
--  BoolAll f (ColRange l h) -> do
--    ld <- decomposeInt l
--    hd <- decomposeInt h
--    n <- newBoolVar val expr
--    (smod,(argsBool,argsInt,argsCol)) <- decomposeSubmodel (0,1,0) $ \([],[oarg],[]) -> do
--      let sexpr = f oarg
--      arg <- newIntVar oarg
--      debug ("BoolAllC: arg="++(show arg)++" oarg="++(show oarg)) $ return ()
--      addConstraint (EGIntExtern $ -1) ([],[arg],[])
--      case val of
--        Just True -> do
--          decomposeBoolEx (Just True) sexpr
--          return ()
--        _ -> do
--          res <- decomposeBool sexpr
--          addConstraint (EGBoolExtern $ -1) ([res],[],[])
--    let force = case val of
--                Just True -> True
--                _ -> False
--    addConstraint (EGAllC smod (length argsBool,length argsInt,length argsCol) force) ([n]++argsBool,[ld,hd]++argsInt,argsCol)
--    return $ Just n
--  BoolAny f (ColRange l h) -> do
--    ld <- decomposeInt l
--    hd <- decomposeInt h
--    n <- newBoolVar val expr
--    (smod,(argsBool,argsInt,argsCol)) <- decomposeSubmodel (0,1,0) $ \([],[oarg],[]) -> do
--      let sexpr = f oarg
--      arg <- newIntVar oarg
--      addConstraint (EGIntExtern $ -1) ([],[arg],[])
--      case val of
--        Just False -> do
--          decomposeBoolEx (Just False) sexpr
--          return ()
--        _ -> do
--          res <- decomposeBool sexpr
--          addConstraint (EGBoolExtern $ -1) ([res],[],[])
--    let force = case val of
--                Just False -> True
--                _ -> False
--    addConstraint (EGAnyC smod (length argsBool,length argsInt,length argsCol) force) ([n]++argsBool,[ld,hd]++argsInt,argsCol)
--    return $ Just n
  BoolAll f c -> do
    cd <- decomposeCol c
    n <- newBoolVar val expr
    (smod,(argsBool,argsInt,argsCol)) <- decomposeSubmodel (0,1,0) $ \([],[oarg],[]) -> do
      let sexpr = f oarg
      arg <- newIntVar oarg
      addConstraint (EGIntExtern $ -1) ([],[arg],[])
      case val of
        Just True -> do   {- in case a BoolAll itself must hold, each submodel must hold too -}
          decomposeBoolEx (Just True) sexpr
          return ()
        _ -> do
          res <- decomposeBool sexpr
          addConstraint (EGBoolExtern $ -1) ([res],[],[])
    let force = 
          case val of
            Just True -> True
            _ -> False
    addConstraint (EGAll smod (length argsBool,length argsInt,length argsCol) force) ([n] ++ argsBool,argsInt,[cd] ++ argsCol)
    return $ Just n
  BoolAny f c -> do
    cd <- decomposeCol c
    n <- newBoolVar val expr
    (smod,(argsBool,argsInt,argsCol)) <- decomposeSubmodel (0,1,0) $ \([],[oarg],[]) -> do
      let sexpr = f oarg
      arg <- newIntVar oarg
      addConstraint (EGIntExtern $ -1) ([],[arg],[])
      case val of
        Just False -> do   {- in case a BoolAny itself may not hold, each submodel may not hold either -}
          decomposeBoolEx (Just False) sexpr
          return ()
        _ -> do
          res <- decomposeBool sexpr
          addConstraint (EGBoolExtern $ -1) ([res],[],[])
    let force = 
          case val of
            Just False -> True
            _ -> False
    addConstraint ((if force then EGAll else EGAny) smod (length argsBool,length argsInt,length argsCol) force) ([n] ++ argsBool,argsInt,[cd] ++ argsCol)
    return $ Just n
  _ -> error $ "Unable to decompose boolean expression: " ++ (show expr) ++ "(== " ++ (show val) ++ ")"

realDecomposeInt :: ModelInt -> DCMonad EGVarId
realDecomposeInt expr = do
  let pIntOp a x b = do
        n <- newIntVar expr
        ad <- decomposeInt a
        bd <- decomposeInt b
        addConstraint x ([],[n,ad,bd],[])
        return n
  case expr of
    Term (ModelIntVar i) -> newIntVar expr
    Plus a b -> pIntOp a EGPlus b
    Minus a b -> pIntOp a EGMinus b
    Mult a b -> pIntOp a EGMult b
    Div a b -> pIntOp a EGDiv b
    Mod a b -> pIntOp a EGMod b
    Abs a -> do
      n <- newIntVar expr
      ad <- decomposeInt a
      addConstraint EGAbs ([],[n,ad],[])
      return n
    At a b -> do
      n <- newIntVar expr
      ad <- decomposeCol a
      bd <- decomposeInt b
      addConstraint EGAt ([],[n,bd],[ad])
      return n
    ColSize a -> do
      n <- newIntVar expr
      ad <- decomposeCol a
      addConstraint EGSize ([],[n],[ad])
      return n
    Channel a -> do
      n <- newIntVar expr
      ad <- decomposeBool a
      addConstraint EGChannel ([ad],[n],[])
      return n
    Cond c t f -> do
      n <- newIntVar expr
      cd <- decomposeBool c
      td <- decomposeInt t
      fd <- decomposeInt f
      addConstraint EGCondInt ([cd],[n,td,fd],[])
      return n
    Fold f i c -> do
      cd <- decomposeCol c
      id <- decomposeInt i
      n <- newIntVar expr
      (smod,(argsBool,argsInt,argsCol)) <- decomposeSubmodel (0,2,0) $ \([],[oacc,oarg],[]) -> do
        let sexpr = f oacc oarg
        acc <- newIntVar oacc
        addConstraint (EGIntExtern $ -2) ([],[acc],[])
        arg <- newIntVar oarg
        addConstraint (EGIntExtern $ -3) ([],[arg],[])
        res <- decomposeInt sexpr
        addConstraint (EGIntExtern $ -1) ([],[res],[])
      addConstraint (EGFold smod (length argsBool,length argsInt,length argsCol)) (argsBool,[n,id]++argsInt,[cd]++argsCol)
      return n
    _ -> error $ "Unable to decompose expression: " ++ (show expr)

listAll :: [a] -> (a -> Maybe b) -> Maybe [b]
listAll [] _ = Just []
listAll (a:b) f = case f a of
  Nothing -> Nothing
  Just r -> case listAll b f of
    Nothing -> Nothing
    Just x -> Just (r:x)

realDecomposeCol :: ModelCol -> DCMonad EGVarId
realDecomposeCol expr = case expr of
  ColList l -> do
    n <- newColVar expr
    ld <- mapM decomposeInt l
    addConstraint (EGList (length l)) ([],ld,[n])
    return n
  ColTerm (ModelColVar i) -> newColVar expr
  ColRange a b -> do
    n <- newColVar expr
    ad <- decomposeInt a
    bd <- decomposeInt b
    addConstraint EGRange ([],[ad,bd],[n])
    return n
  ColCat a b -> do
    n <- newColVar expr
    ad <- decomposeCol a
    bd <- decomposeCol b
    addConstraint EGCat ([],[],[n,ad,bd])
    return n
{-  ColSlice f n c -> do
    nn <- newColVar expr
    cd <- decomposeCol c
    let fd x = debug ("ColSlice: f("++(show x)++")="++(show $ f $ transform invConstTrans x)) $ transform constTrans $ f $ transform invConstTrans x
    let nd = transform constTrans n
    addConstraint (EGSlice fd nd) ([],[],[nn,cd])
    return nn -}
  ColSlice f nn c -> do
    cd <- decomposeCol c
    nd <- decomposeInt nn
    n <- newColVar expr
    (smod,(argsBool,argsInt,argsCol)) <- decomposeSubmodel (0,1,0) $ \([],[oarg],[]) -> do
      let sexpr = f oarg
      arg <- newIntVar oarg
      addConstraint (EGIntExtern $ -2) ([],[arg],[])
      res <- decomposeInt sexpr
      addConstraint (EGIntExtern $ -1) ([],[res],[])
    addConstraint (EGSlice smod (length argsBool,length argsInt,length argsCol)) (argsBool,[nd]++argsInt,[n,cd]++argsCol)
    return n
  ColMap f c -> do
    cd <- decomposeCol c
    n <- newColVar expr
    (smod,(argsBool,argsInt,argsCol)) <- decomposeSubmodel (0,1,0) $ \([],[oarg],[]) -> do
      let sexpr = f oarg
      arg <- newIntVar oarg
      addConstraint (EGIntExtern $ -2) ([],[arg],[])
      res <- decomposeInt sexpr
      addConstraint (EGIntExtern $ -1) ([],[res],[])
    addConstraint (EGMap smod (length argsBool,length argsInt,length argsCol)) (argsBool,argsInt,[n,cd]++argsCol)
    return n
  _ -> error $ "Unable to decompose collection: " ++ (show expr)
