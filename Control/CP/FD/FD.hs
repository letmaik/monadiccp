{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.CP.FD.FD (
  module Data.Expr.Sugar,
  FDInstance,
  FDSolver(..),
  FDSpecInfo,
  FDSpecInfoBool(..), FDSpecInfoInt(..), FDSpecInfoCol(..),
  liftFD, addFD,
  SpecFn, SpecFnRes, SpecResult(..),
  getBoolSpec_, getIntSpec_, getColSpec_,
  getBoolSpec,  getIntSpec,  getColSpec,
  getEdge, markEdge,
  setFailed,
  getLevel,
  getIntVal, getBoolVal, getColVal,
  getIntTerm, getBoolTerm, getColTerm,
  getSingleIntTerm,
  getDefBoolSpec, getDefIntSpec, getDefColSpec,
  getFullBoolSpec, getFullIntSpec, getFullColSpec,
  getColItems,
  fdSpecInfo_spec,
  specInfoBoolTerm, specInfoIntTerm,
  Control.CP.FD.FD.newInt, Control.CP.FD.FD.newBool, Control.CP.FD.FD.newCol,
  procSubModel, procSubModelEx, specSubModelEx,
  runFD,
  setMinimizeVar, boundMinimize, getMinimizeTerm, getMinimizeVar,
  fdNewvar,
) where

import Control.Monad.State.Lazy
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set(Set)

import Control.CP.Debug
import Data.Expr.Sugar
import Data.Expr.Data
-- import Control.CP.FD.Expr.Util
import Control.CP.FD.Model
import Control.CP.FD.Decompose
import Control.CP.FD.Graph
import Control.CP.SearchTree
import Control.CP.ComposableTransformers
import Control.CP.EnumTerm
import Control.CP.Solver
import Control.Mixin.Mixin

-- | state kept by FDInstance, in addition to the underlying solver's internal state
data FDSolver s => FDState s = FDState {
  -- | expression representing unprocessed constraints
  fdsExpr :: Model,
  -- | model being processed now
  fdsModel :: Maybe EGModel,
  -- | private data for the decomposer (kept to optimize constraints which aren't added in one go)
  fdsDecomp :: DecompData,
  -- | when adding constraints, the EGEdgeId's occurring in the decomposed model
  fdsNewEdges :: Set EGEdgeId,
  fdsDoneEdges :: Set EGEdgeId,
  -- | expressions that need to be decomposed
  fdsForceBool :: [ModelBool], fdsForcedBool :: Map ModelBool (FDBoolTerm s),
  fdsForceInt :: [ModelInt], fdsForcedInt :: Map ModelInt (FDIntTerm s),
  fdsForceCol :: [ModelCol],
  -- | variable counter
  fdsVars :: Int,

  -- | already introduced integer variables/terms/constants/expressions 
  fdsIntVars :: Map EGVarId (FDSpecInfoInt s),
  -- | needed sets of possible types
  fdsIntVarTypes :: Map EGVarId (Set (FDIntSpecTypeSet s)),
  -- | which variables are being decomposed right now
  fdsIntVarBusy :: Set EGVarId,
  -- | which nodes are unified with which others
  fdsIntUnifies :: Map EGVarId (Set EGVarId),

  -- | already introduced boolean variables/terms/constants/expressions 
  fdsBoolVars :: Map EGVarId (FDSpecInfoBool s),
  fdsBoolVarTypes :: Map EGVarId (Set (FDBoolSpecTypeSet s)),
  fdsBoolVarBusy :: Set EGVarId,
  fdsBoolUnifies :: Map EGVarId (Set EGVarId),
  -- | already introduced collection variables/terms/constants/expressions 
  fdsColVars :: Map EGVarId (FDSpecInfoCol s),
  fdsColVarTypes :: Map EGVarId (Set (FDColSpecTypeSet s)),
  fdsColVarBusy :: Set EGVarId,
  fdsColUnifies :: Map EGVarId (Set EGVarId),

  -- | db of specifiers
  fdsDb :: SpecDb s,

  -- | solver is failed?
  fdsFailed :: Bool,

  -- | level of nesting
  fdsLevel :: Int,

  -- | levels of dummyness
  fdsDummyLevel :: Int,

  fdsMinimizeVar :: Maybe ModelInt,
  fdsMinimizeTerm :: Maybe (FDIntTerm s)
}

myFromJust str m = case m of
  Nothing -> error $ "myFromJust: " ++ str
  Just x -> x

unifyInts a b = do
  s <- get
  let sa = Map.findWithDefault (Set.singleton a) a (fdsIntUnifies s)
  let sb = Map.findWithDefault (Set.singleton b) b (fdsIntUnifies s)
  let sc = Set.union sa sb
  put s { fdsIntUnifies = foldr (\a b -> Map.insert a sc b) (fdsIntUnifies s) $ Set.toList sc }

unifyBools a b = do
  s <- get
  let sa = Map.findWithDefault (Set.singleton a) a (fdsBoolUnifies s)
  let sb = Map.findWithDefault (Set.singleton b) b (fdsBoolUnifies s)
  let sc = Set.union sa sb
  put s { fdsBoolUnifies = foldr (\a b -> Map.insert a sc b) (fdsBoolUnifies s) $ Set.toList sc }

unifyCols a b = do
  s <- get
  let sa = Map.findWithDefault (Set.singleton a) a (fdsColUnifies s)
  let sb = Map.findWithDefault (Set.singleton b) b (fdsColUnifies s)
  let sc = Set.union sa sb
  put s { fdsColUnifies = foldr (\a b -> Map.insert a sc b) (fdsColUnifies s) $ Set.toList sc }

mapVals :: Show b => (a -> Maybe b) -> [a] -> [String]
mapVals f l = nub $ sort $ map show $ catMaybes $ map f l

dumpSpec :: FDSolver s => FDState s -> String
dumpSpec s = 
  foldl (++) "" (map (\(i,r) -> "i" ++ (show $ unVarId i) ++ "\n" ++ foldl (++) "" (map (\x -> "  "++x++"\n") (mapVals (fdspIntSpec r) (Nothing : (map Just $ Set.toList $ fdspIntTypes r))))) $ Map.toList (fdsIntVars s)) ++
  foldl (++) "" (map (\(i,r) -> "b" ++ (show $ unVarId i) ++ "\n" ++ foldl (++) "" (map (\x -> "  "++x++"\n") (mapVals (fdspBoolSpec r) (Nothing : (map Just $ Set.toList $ fdspBoolTypes r))))) $ Map.toList (fdsBoolVars s)) ++
  foldl (++) "" (map (\(i,r) -> "c" ++ (show $ unVarId i) ++ "\n" ++ foldl (++) "" (map (\x -> "  "++x++"\n") (mapVals (fdspColSpec r) (Nothing : (map Just $ Set.toList $ fdspColTypes r))))) $ Map.toList (fdsColVars s))

setMinimizeVar :: (Show (FDIntTerm s), FDSolver s) => ModelInt -> FDInstance s ()
setMinimizeVar v = do
  s <- get
  case Map.lookup v (fdsForcedInt s) of
    Just t -> debug ("setMinimizeVar: (cached) var="++(show v)++" term="++(show t)) $ put s { fdsMinimizeVar = Just v, fdsMinimizeTerm = Just t }
    Nothing -> do
      var <- getSingleIntTerm v
      s2 <-  get
      debug ("setMinimizeVar: (not cached) var="++(show v)++" term="++(show var)) $ put s2 { fdsMinimizeVar = Just v, fdsMinimizeTerm = Just var }

getMinimizeVar :: (Show (FDIntTerm s), FDSolver s) => FDInstance s (Maybe ModelInt)
getMinimizeVar = do
  s <- get
  return $ fdsMinimizeVar s

getMinimizeTerm :: (Show (FDIntTerm s), FDSolver s) => FDInstance s (Maybe (FDIntTerm s))
getMinimizeTerm = do
  s <- get
  debug ("getMinimizeTerm: "++(show $ fdsMinimizeTerm s)) $ return ()
  return (fdsMinimizeTerm s)
--  case (fdsMinimizeTerm s) of
--    q@(Just _) -> return q
--    Nothing -> case (fdsMinimizeVar s) of
--      Nothing -> return Nothing
--      Just v -> do
--        q <- getSingleIntTerm v
--        put s { fdsMinimizeTerm = Just q }
--        return $ Just q

boundMinimize :: (Show (FDIntTerm s), FDSolver s, EnumTerm s (FDIntTerm s), Integral (TermBaseType s (FDIntTerm s))) => NewBound (FDInstance s)
boundMinimize = do
  bound <- getMinimizeTerm
  case bound of
    Nothing -> error "no bound variable defined"
    Just bndvar -> do
      x <- liftFD $ getValue bndvar
      case x of
        Just val -> do
          con <- liftFD $ fdConstrainIntTerm bndvar (toInteger val)
          let f = Bound (\x -> (Add (Right con) x))
          return f
        _ -> error "bound variable is not assigned"

runFD :: FDSolver s => FDInstance s a -> s a
runFD (FDInstance { unFDInstance = u }) = evalStateT u baseFDState

linkExterns :: FDSolver s => (Int -> Maybe (FDSpecInfoBool s), Int -> Maybe (FDSpecInfoInt s), Int -> Maybe (FDSpecInfoCol s)) -> EGEdgeId -> FDInstance s ()
linkExterns (sfb,sfi,sfc) id = do
  s <- get
  let Just jm = fdsModel s
  let Just edge = Map.lookup id $ egmEdges jm
  case (egeCons edge) of
    EGBoolExtern p -> do
      case sfb p of
        Nothing -> return ()
        Just spec -> do
          let [varid] = boolData $ egeLinks edge
          if (Map.member varid $ fdsBoolVars s) then error "double bool import" else return ()
          put $ s { fdsBoolVars = Map.insert varid spec $ fdsBoolVars s, fdsBoolVarTypes = Map.delete varid $ fdsBoolVarTypes s }
      markEdge id
    EGIntExtern p -> do
      case sfi p of
        Nothing -> return ()
        Just spec -> do
          let [varid] = intData $ egeLinks edge
          if (Map.member varid $ fdsIntVars s) then error "double int import" else return ()
          put $ s { fdsIntVars = Map.insert varid spec $ fdsIntVars s, fdsIntVarTypes = Map.delete varid $ fdsIntVarTypes s }
      markEdge id
    EGColExtern p -> do
      case sfc p of
        Nothing -> return ()
        Just spec -> do
          let [varid] = colData $ egeLinks edge
          if (Map.member varid $ fdsColVars s) then error "double col import" else return ()
          put $ s { fdsColVars = Map.insert varid spec $ fdsColVars s, fdsColVarTypes = Map.delete varid $ fdsColVarTypes s }
      markEdge id
    _ -> return ()

procSubModel :: FDSolver s => EGModel -> (Int -> FDSpecInfoBool s, Int -> FDSpecInfoInt s, Int -> FDSpecInfoCol s) -> FDInstance s ()
procSubModel sm (fb,fi,fc) = procSubModelEx sm (Just . fb,Just . fi,Just . fc)

procSubModelEx :: FDSolver s => EGModel -> (Int -> Maybe (FDSpecInfoBool s), Int -> Maybe (FDSpecInfoInt s), Int -> Maybe (FDSpecInfoCol s)) -> FDInstance s ()
procSubModelEx sm specfn = do
  s <- get
  let ss = baseFDState {
    fdsModel = Just sm,
    fdsVars = fdsVars s,
    fdsFailed = fdsFailed s,
    fdsLevel = 1 + fdsLevel s
  }
  put ss
  initForModel
  s2 <- get
  mapM_ (linkExterns specfn) $ Set.toList $ fdsNewEdges s2
  process
  s3 <- get
  put $ s { fdsFailed = fdsFailed s || fdsFailed s3, fdsVars = fdsVars s3 }

getLevel :: FDSolver s => FDInstance s Int
getLevel = do
  s <- get
  return $ fdsLevel s

-- specSubModelEx :: FDSolver s => EGModel -> (Int -> Maybe (FDSpecInfoBool s), Int -> Maybe (FDSpecInfoInt s), Int -> Maybe (FDSpecInfoCol s)) -> FDInstance s ()
specSubModelEx sm specfn = do
  s <- get
  let ss = baseFDState {
    fdsModel = Just sm,
    fdsVars = fdsVars s,
    fdsFailed = fdsFailed s,
    fdsLevel = 1 + fdsLevel s
  }
  put ss
  initForModel
  s2 <- get
  mapM_ (linkExterns specfn) $ Set.toList $ fdsNewEdges s2
  s3 <- get
  put s3 { fdsDummyLevel = 1 }
  processEx False
  s4 <- get
  put $ s { fdsFailed = fdsFailed s || fdsFailed s4, fdsVars = fdsVars s4 }
  return (fdsBoolVars s4, fdsIntVars s4, fdsColVars s4)

optimizeSetSet :: Ord a => Set (Set a) -> Set (Set a)
optimizeSetSet x = 
  let (min,xx) = Set.deleteFindMin x
      inter = Set.fold Set.intersection min xx
      in if Set.null inter then x else Set.singleton inter

optimizeVarTypes :: FDSolver s => FDInstance s ()
optimizeVarTypes = do
  s <- get
  put $ s {
    fdsBoolVarTypes = Map.map optimizeSetSet $ fdsBoolVarTypes s,
    fdsIntVarTypes = Map.map optimizeSetSet $ fdsIntVarTypes s,
    fdsColVarTypes = Map.map optimizeSetSet $ fdsColVarTypes s
  }

checkNeedSpecType var typ db = any (Set.member typ) $ Set.toList $ Map.findWithDefault Set.empty var db

decompSpec fn db un unfn ex vars typs = do
  s <- get
  let tri [] = do
        debug ("decompSpec vars="++(show vars)++": no spec left, failing") $ return ()
        return Nothing
      tri (((_,_,id),_):rest) | not (Set.member id vars) = tri rest
      tri ((key@(_,_,id),(eid,s)):rest) = case ex s of
        Nothing -> tri rest
        Just spec -> do
          res <- spec
          case res of
            SpecResNone -> tri rest
            SpecResSpec (typ,spec) -> if Set.member typ typs
              then do
                rr <- liftFD spec
                debug ("decompSpec: got spec: " ++ (show rr)) $ return ()
                fn (Set.findMin vars) typ rr
                case eid of
                  Nothing -> return ()
                  Just e -> do
                    debug ("decompSpec: marking edge "++(show e)) $ return ()
                    markEdge e
                return $ Just (typ,rr)
              else tri rest
            SpecResUnify v -> do
              unfn id v
              decompSpec fn db un unfn ex vars typs
  tri $ Map.toDescList $ db

decompBestHelp id spec fn unfn eid prio db = do
  res <- spec
  case res of
    SpecResNone -> do
      debug ("decompBestHelp: level "++(show prio)++" specifier for var "++(show id)++" by edge "++(show eid)++" has failed") $ return ()
      return ()
    SpecResSpec (typ,ss) -> if checkNeedSpecType id typ db
      then do
        rr <- liftFD ss
        res <- fn id typ rr
        case eid of
          Nothing -> return ()
          Just e -> do
            debug ("decompBestHelp: marking edge "++(show e)) $ return ()
            markEdge e
            return ()
        return res
      else do
        debug ("decompBestHelp: typ "++(show typ)++" specifier for id "++(show id)++" seems not needed") $ return ()
        return ()
    SpecResUnify v -> do
      unfn id v
      return ()

decompBest :: FDSolver s => FDInstance s Bool
decompBest = do
  s1 <- debug "in decompBest: get" $ get
  debug "in decompBest" $ return ()
  if Map.null $ fdsDb s1
    then return False
    else do
      let (((prio,knd,id),(eid,spec)),nm) = Map.deleteFindMax $ fdsDb $ debug "s1?" s1
          s2 = debug ("got best spec: prio="++(show prio)++", knd="++(show knd)++", id="++(show id)++", eid="++(show eid)++", spec=?") $ s1 { fdsDb = nm }
      put s2
      case knd of
        FDTBool -> do
          let s3 = s2 { fdsBoolVarBusy = Set.insert id $ fdsBoolVarBusy s2 }
          put s3
          let Just j = fdsBoolSel spec
          decompBestHelp id j addBoolVar unifyBools eid prio $ fdsBoolVarTypes s3
          s4 <- get
          put $ s4 { fdsBoolVarBusy = Set.delete id $ fdsBoolVarBusy s4 }
        FDTInt -> do
          let s3 = s2 { fdsIntVarBusy = Set.insert id $ fdsIntVarBusy s2 }
          put s3
          let Just j = fdsIntSel spec
          decompBestHelp id j addIntVar unifyInts eid prio $ fdsIntVarTypes s3
          s4 <- get
          put $ s4 { fdsIntVarBusy = Set.delete id $ fdsIntVarBusy s4 }
        FDTCol -> do
          let s3 = s2 { fdsColVarBusy = Set.insert id $ fdsColVarBusy s2 }
          put s3
          let Just j = fdsColSel spec
          decompBestHelp id j addColVar unifyCols eid prio $ fdsColVarTypes s3
          s4 <- get
          put $ s4 { fdsColVarBusy = Set.delete id $ fdsColVarBusy s4 }
      return True

decompDefaultBool :: FDSolver s => FDInstance s Bool
decompDefaultBool = do
  s1 <- get
  if Map.null $ fdsBoolVarTypes s1
    then return False
    else do
      let ((varid,set),nm) = Map.deleteFindMin $ fdsBoolVarTypes s1
          s2 = s1 { fdsBoolVarTypes = nm }
      put s2
      if Set.null set
        then return True
        else do
          defaultBoolDecomp varid Nothing
          return True

decompDefaultInt :: FDSolver s => FDInstance s Bool
decompDefaultInt = do
  s1 <- get
  if Map.null $ fdsIntVarTypes s1
    then return False
    else do
      let ((varid,set),nm) = Map.deleteFindMin $ fdsIntVarTypes s1
          s2 = s1 { fdsIntVarTypes = nm }
      put s2
      if Set.null set
        then return True
        else do
          defaultIntDecomp varid Nothing
          return True

defaultBoolDecomp :: FDSolver s => EGVarId -> (Maybe (FDBoolSpecTypeSet s)) -> FDInstance s (Maybe (FDBoolSpecType s, FDBoolSpec s))
defaultBoolDecomp var typs = do
  s <- get
  if fdsDummyLevel s > 0 
    then return Nothing
    else do
      vt <- liftFD $ fdTypeVarBool
      let Just jt = typs
      if (isNothing typs || not (Set.null $ Set.intersection vt jt))
        then do
          Just v <- fdNewvar
          let (ty,sp) = fdBoolSpec_term v
          rs <- liftFD sp
          addBoolVar var ty (rs, Nothing)
          return $ Just (ty,rs)
        else return Nothing

defaultIntDecomp :: FDSolver s => EGVarId -> (Maybe (FDIntSpecTypeSet s)) -> FDInstance s (Maybe (FDIntSpecType s, FDIntSpec s))
defaultIntDecomp var typs = do
  s <- get
  if fdsDummyLevel s > 0
    then return Nothing
    else do
      vt <- liftFD $ fdTypeVarInt
      let Just jt = typs
      if (isNothing typs || not (Set.null $ Set.intersection vt jt))
        then do
          Just v <- fdNewvar
          let (ty,sp) = fdIntSpec_term v
          rs <- liftFD sp
          addIntVar var ty (rs, Nothing)
          return $ Just (ty,rs)
        else return Nothing

getBoolSpec_ :: FDSolver s => EGVarId -> FDBoolSpecTypeSet s -> FDInstance s (Maybe (FDBoolSpecType s, FDBoolSpec s))
getBoolSpec_ var typs = do
  s <- get
  let vars = Map.findWithDefault (Set.singleton var) var $ fdsBoolUnifies s
  getBoolSpec__ vars typs

getBoolSpec__ :: FDSolver s => Set EGVarId -> FDBoolSpecTypeSet s -> FDInstance s (Maybe (FDBoolSpecType s, FDBoolSpec s))
getBoolSpec__ vars typs = do
  s <- get
  let mp = foldl (\b a -> case Map.lookup a (fdsBoolVars s) of { Nothing -> b; Just x -> case b of { Nothing -> Just x; Just r -> Just $ unionSpecBool r x }}) Nothing (Set.toList vars)
  let sp = Set.intersection (maybe Set.empty fdspBoolTypes mp) typs
  let db = fdsDb s
  if Set.null sp
    then if not (Set.null $ Set.intersection vars $ fdsBoolVarBusy s)
      then return Nothing
      else do
        put $ s { fdsBoolVarBusy = Set.union vars $ fdsBoolVarBusy s }
        res <- decompSpec addBoolVar db (\x -> Map.lookup x $ fdsBoolUnifies s) unifyBools fdsBoolSel vars typs
        s2 <- get
        put $ s2 { fdsBoolVarBusy = Set.difference (fdsBoolVarBusy s) vars }
        case res of
          Just (tp,(sp,_)) -> return $ Just (tp,sp)
          _ -> defaultBoolDecomp (Set.findMin vars) $ Just typs
    else do
      let lp = Set.findMin sp
      let Just jmp = mp
      let Just j = fdspBoolSpec jmp $ Just lp
      return $ Just (lp,j)

getBoolSpec :: FDSolver s => EGVarId -> FDInstance s (Maybe (FDBoolSpec s))
getBoolSpec var = do
  s <- allBoolSpec
  q <- getBoolSpec_ var s
  return $ case q of
    Just (_,x) -> Just x
    Nothing -> Nothing

getIntSpec_ :: FDSolver s => EGVarId -> FDIntSpecTypeSet s -> FDInstance s (Maybe (FDIntSpecType s, FDIntSpec s))
getIntSpec_ var typs = do
  s <- get
  let vars = Map.findWithDefault (Set.singleton var) var $ fdsIntUnifies s
  getIntSpec__ vars typs

getIntSpec__ :: FDSolver s => Set EGVarId -> FDIntSpecTypeSet s -> FDInstance s (Maybe (FDIntSpecType s, FDIntSpec s))
getIntSpec__ vars typs = do
  s <- get
  let mp = foldl (\b a -> case Map.lookup a (fdsIntVars s) of { Nothing -> b; Just x -> case b of { Nothing -> Just x; Just r -> Just $ unionSpecInt r x }}) Nothing $ Set.toList vars
  let sp = Set.intersection (maybe Set.empty fdspIntTypes mp) typs
  let db = fdsDb s
  if Set.null sp
    then if not (Set.null $ Set.intersection vars $ fdsIntVarBusy s)
      then do
        debug ("getIntSpec__ "++(show (vars,typs))++": busy, failing") $ return ()
        return Nothing
      else do
        put $ s { fdsIntVarBusy = Set.union vars $ fdsIntVarBusy s }
        res <- decompSpec addIntVar db (\x -> Map.lookup x $ fdsIntUnifies s) unifyInts fdsIntSel vars typs
        s2 <- get
        put $ s2 { fdsIntVarBusy = Set.difference (fdsIntVarBusy s) vars }
        case res of
          Just (tp,(sp,_)) -> return $ Just (tp,sp)
          _ -> defaultIntDecomp (Set.findMin vars) $ Just typs
    else do
      let lp = Set.findMin sp
      let Just jmp = mp
      let Just j = fdspIntSpec jmp $ Just lp
      return $ Just (lp,j)

getIntSpec :: FDSolver s => EGVarId -> FDInstance s (Maybe (FDIntSpec s))
getIntSpec var = do
  s <- allIntSpec
  q <- getIntSpec_ var s
  return $ case q of
    Just (_,x) -> Just x
    Nothing -> Nothing

getColSpec_ :: FDSolver s => EGVarId -> FDColSpecTypeSet s -> FDInstance s (Maybe (FDColSpecType s, FDColSpec s))
getColSpec_ var typs = do
  s <- get
  let vars = Map.findWithDefault (Set.singleton var) var $ fdsColUnifies s
  getColSpec__ vars typs

getColSpec__ :: FDSolver s => Set EGVarId -> FDColSpecTypeSet s -> FDInstance s (Maybe (FDColSpecType s, FDColSpec s))
getColSpec__ vars typs = do
  s <- get
  let mp = foldl (\b a -> case Map.lookup a (fdsColVars s) of { Nothing -> b; Just x -> case b of { Nothing -> Just x; Just r -> Just $ unionSpecCol r x }}) Nothing (Set.toList vars)
  let sp = Set.intersection (maybe Set.empty fdspColTypes mp) typs
  let db = fdsDb s
  if Set.null sp
    then if not (Set.null $ Set.intersection vars $ fdsColVarBusy s)
      then return Nothing
      else do
        put $ s { fdsColVarBusy = Set.union vars $ fdsColVarBusy s }
        res <- decompSpec addColVar db (\x -> Map.lookup x $ fdsColUnifies s) unifyCols fdsColSel vars typs
        s2 <- get
        put $ s2 { fdsColVarBusy = Set.difference (fdsColVarBusy s) vars }
        case res of
          Just (tp,(sp,_)) -> return $ Just (tp,sp)
          _ -> return Nothing
    else do
      let lp = Set.findMin sp
      let Just jmp = mp
      let Just j = fdspColSpec jmp $ Just lp
      return $ Just (lp,j)

getColSpec :: (Show (FDColSpec s), FDSolver s) => EGVarId -> FDInstance s (Maybe (FDColSpec s))
getColSpec var = do
  s <- allColSpec
  q <- getColSpec_ var s
  return $ case q of
    Just (_,x) -> Just x
    Nothing -> Nothing

-- | initial FDState state 
baseFDState :: FDSolver s => FDState s
baseFDState = FDState {
  fdsVars = 0,
  fdsExpr = BoolConst True,
  fdsForceBool = [],
  fdsForcedBool = Map.empty,
  fdsForceInt = [],
  fdsForcedInt = Map.empty,
  fdsForceCol = [],
  fdsModel = Nothing,
  fdsNewEdges = Set.empty,
  fdsDoneEdges = Set.empty,
  fdsDecomp = baseDecompData,
  fdsIntVars = Map.empty,
  fdsIntVarTypes = Map.empty,
  fdsIntVarBusy = Set.empty,
  fdsIntUnifies = Map.empty,
  fdsBoolVars = Map.empty,
  fdsBoolVarTypes = Map.empty,
  fdsBoolVarBusy = Set.empty,
  fdsBoolUnifies = Map.empty,
  fdsColVars = Map.empty,
  fdsColVarTypes = Map.empty,
  fdsColVarBusy = Set.empty,
  fdsColUnifies = Map.empty,
  fdsDb = Map.empty,
  fdsFailed = False,
  fdsLevel = 0,
  fdsDummyLevel = 0,
  fdsMinimizeVar = Nothing,
  fdsMinimizeTerm = Nothing
}

edgesLeft :: FDSolver s => FDInstance s Bool
edgesLeft = get >>= return . Set.null . fdsNewEdges

-- | run the second argument as long as the first one produces true
whileM :: Monad m => m Bool -> m a -> m ()
whileM cond act = do
  x <- cond
  if x
    then do
      act
      whileM cond act
    else return ()

whileM_ :: Monad m => m Bool -> m ()
whileM_ cond = whileM cond $ return ()

-- | a label for an FDInstance; must store the FDState plus the Solver's internal state
data FDSolver s => FDLabel s = FDLabel {
  fdlState :: FDState s,
  fdlLabel :: Label s
}

-- | definition of FDInstance, a Solver wrapper that adds power to post boolean expressions as constraints
newtype FDSolver s => FDInstance s a = FDInstance { unFDInstance :: StateT (FDState s) s a }
  deriving (Monad, MonadState (FDState s))

-- | helper function to combine two Maybe's
joinWith :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
joinWith f a b = case (a,b) of
  (Nothing,_) -> b
  (_,Nothing) -> a
  (Just x,Just y) -> Just $ f x y

-- | lift a monad action for the underlying solver to a monad action for an FDInstance around it
liftFD :: FDSolver s => s a -> FDInstance s a
liftFD = FDInstance . lift

liftFDTree :: (FDSolver s, MonadTree m, TreeSolver m ~ (FDInstance s)) => Tree s a -> m a
liftFDTree = mapTree liftFD

data SpecResult t =
    SpecResNone
  | SpecResSpec t
  | SpecResUnify EGVarId

type SpecBool s = FDInstance s (SpecResult (FDBoolSpecType s, s (FDBoolSpec s, Maybe EGBoolPar)))
type SpecInt s = FDInstance s (SpecResult (FDIntSpecType s, s (FDIntSpec s, Maybe EGPar)))
type SpecCol s = FDInstance s (SpecResult (FDColSpecType s, s (FDColSpec s, Maybe EGColPar)))

type SpecFnRes s = 
  (
    [(Int, EGVarId, Bool, SpecBool s)],
    [(Int, EGVarId, Bool, SpecInt s)],
    [(Int, EGVarId, Bool, SpecCol s)]
  )

type SpecFn s = EGEdge -> SpecFnRes s

data TermType = FDTBool | FDTInt | FDTCol
  deriving (Eq,Ord,Bounded,Enum,Show)

fdsBoolSel x = case x of
  FDSBool a -> Just a
  _ -> Nothing
fdsIntSel x = case x of
  FDSInt a -> Just a
  _ -> Nothing
fdsColSel x = case x of
  FDSCol a -> Just a
  _ -> Nothing

data TermTypeSpec s = FDSBool (SpecBool s) | FDSInt (SpecInt s) | FDSCol (SpecCol s)

instance Show (TermTypeSpec s) where
  show (FDSBool _) = "FDSBool"
  show (FDSInt _) = "FDSInt"
  show (FDSCol _) = "FDSCol"

type SpecDb s = Map (Int,TermType,EGVarId) (Maybe EGEdgeId,TermTypeSpec s)

addBoolSpec :: FDSolver s => SpecDb s -> (Int,EGVarId,Maybe EGEdgeId,SpecBool s) -> SpecDb s
addBoolSpec db (prio,var,eid,spec) = Map.insert (prio,FDTBool,var) (eid,FDSBool spec) db

addIntSpec :: FDSolver s => SpecDb s -> (Int,EGVarId,Maybe EGEdgeId,SpecInt s) -> SpecDb s
addIntSpec db (prio,var,eid,spec) = Map.insert (prio,FDTInt,var) (eid,FDSInt spec) db

addColSpec :: FDSolver s => SpecDb s -> (Int,EGVarId,Maybe EGEdgeId,SpecCol s) -> SpecDb s
addColSpec db (prio,var,eid,spec) = Map.insert (prio,FDTCol,var) (eid,FDSCol spec) db

emptyFDSpecInfoBool :: FDSolver s => EGVarId -> FDState s -> FDSpecInfoBool s
emptyFDSpecInfoBool v s = FDSpecInfoBool { fdspBoolSpec = const Nothing, fdspBoolVar = Just v, fdspBoolVal = getBoolVal_ v s, fdspBoolTypes = Set.empty }
emptyFDSpecInfoInt :: FDSolver s => EGVarId -> FDState s -> FDSpecInfoInt s
emptyFDSpecInfoInt v s = FDSpecInfoInt { fdspIntSpec = const Nothing, fdspIntVar = Just v, fdspIntVal = getIntVal_ v s, fdspIntTypes = Set.empty }
emptyFDSpecInfoCol :: FDSolver s => EGVarId -> FDState s -> FDSpecInfoCol s
emptyFDSpecInfoCol v s = FDSpecInfoCol { fdspColSpec = const Nothing, fdspColVar = Just v, fdspColVal = getColVal_ v s, fdspColTypes = Set.empty }

data FDSpecInfoBool s = FDSpecInfoBool { fdspBoolSpec :: Maybe (FDBoolSpecType s) -> Maybe (FDBoolSpec s), fdspBoolVar :: Maybe EGVarId, fdspBoolVal :: Maybe EGBoolPar, fdspBoolTypes :: Set (FDBoolSpecType s) }
data FDSpecInfoInt s = FDSpecInfoInt   { fdspIntSpec  :: Maybe (FDIntSpecType s)  -> Maybe (FDIntSpec s),  fdspIntVar ::  Maybe EGVarId, fdspIntVal ::  Maybe EGPar, fdspIntTypes :: Set (FDIntSpecType s) }
data FDSpecInfoCol s = FDSpecInfoCol   { fdspColSpec  :: Maybe (FDColSpecType s)  -> Maybe (FDColSpec s),  fdspColVar ::  Maybe EGVarId, fdspColVal ::  Maybe EGColPar, fdspColTypes :: Set (FDColSpecType s) }

unionSpecBool (FDSpecInfoBool { fdspBoolSpec = s1, fdspBoolVar = n1, fdspBoolVal = v1, fdspBoolTypes = t1 }) (FDSpecInfoBool { fdspBoolSpec = s2, fdspBoolVar = n2, fdspBoolVal = v2, fdspBoolTypes = t2 }) =
  FDSpecInfoBool { fdspBoolSpec = \t -> (s1 t) `mplus` (s2 t), fdspBoolVal = v1 `mplus` v2, fdspBoolVar = n1 `mplus` n2, fdspBoolTypes = Set.union t1 t2 }
unionSpecInt (FDSpecInfoInt { fdspIntSpec = s1, fdspIntVar = n1, fdspIntVal = v1, fdspIntTypes = t1 }) (FDSpecInfoInt { fdspIntSpec = s2, fdspIntVar = n2, fdspIntVal = v2, fdspIntTypes = t2 }) =
  FDSpecInfoInt { fdspIntSpec = \t -> (s1 t) `mplus` (s2 t), fdspIntVal = v1 `mplus` v2, fdspIntVar = n1 `mplus` n2, fdspIntTypes = Set.union t1 t2 }
unionSpecCol (FDSpecInfoCol { fdspColSpec = s1, fdspColVar = n1, fdspColVal = v1, fdspColTypes = t1 }) (FDSpecInfoCol { fdspColSpec = s2, fdspColVar = n2, fdspColVal = v2, fdspColTypes = t2 }) =
  FDSpecInfoCol { fdspColSpec = \t -> (s1 t) `mplus` (s2 t), fdspColVal = v1 `mplus` v2, fdspColVar = n1 `mplus` n2, fdspColTypes = Set.union t1 t2 }

instance (Ord (FDBoolSpec s), Ord (FDBoolSpecType s)) => Eq (FDSpecInfoBool s) where
  a == b = (compare a b) == EQ
instance (Ord (FDBoolSpec s), Ord (FDBoolSpecType s)) => Ord (FDSpecInfoBool s) where
  compare (FDSpecInfoBool { fdspBoolSpec = s1, fdspBoolVar = r1, fdspBoolVal = v1, fdspBoolTypes = t1 }) (FDSpecInfoBool { fdspBoolSpec = s2, fdspBoolVar = r2, fdspBoolVal = v2, fdspBoolTypes = t2 }) =
    compare r1 r2 <<>> compare v1 v2 <<>> compare (s1 Nothing) (s2 Nothing) <<>> compare (Map.fromList $ map (\x -> (x,s1 $ Just x)) $ Set.toList t1) (Map.fromList $ map (\x -> (x,s2 $ Just x)) $ Set.toList t2)

instance (Ord (FDIntSpec s), Ord (FDIntSpecType s)) => Eq (FDSpecInfoInt s) where
  a == b = (compare a b) == EQ
instance (Ord (FDIntSpec s), Ord (FDIntSpecType s)) => Ord (FDSpecInfoInt s) where
  compare (FDSpecInfoInt { fdspIntSpec = s1, fdspIntVar = r1, fdspIntVal = v1, fdspIntTypes = t1 }) (FDSpecInfoInt { fdspIntSpec = s2, fdspIntVar = r2, fdspIntVal = v2, fdspIntTypes = t2 }) =
    compare r1 r2 <<>> compare v1 v2 <<>> compare (s1 Nothing) (s2 Nothing) <<>> compare (Map.fromList $ map (\x -> (x,s1 $ Just x)) $ Set.toList t1) (Map.fromList $ map (\x -> (x,s2 $ Just x)) $ Set.toList t2)

instance (Ord (FDColSpec s), Ord (FDColSpecType s)) => Eq (FDSpecInfoCol s) where
  a == b = (compare a b) == EQ
instance (Ord (FDColSpec s), Ord (FDColSpecType s)) => Ord (FDSpecInfoCol s) where
  compare (FDSpecInfoCol { fdspColSpec = s1, fdspColVar = r1, fdspColVal = v1, fdspColTypes = t1 }) (FDSpecInfoCol { fdspColSpec = s2, fdspColVar = r2, fdspColVal = v2, fdspColTypes = t2 }) =
    compare r1 r2 <<>> compare v1 v2 <<>> compare (s1 Nothing) (s2 Nothing) <<>> compare (Map.fromList $ map (\x -> (x,s1 $ Just x)) $ Set.toList t1) (Map.fromList $ map (\x -> (x,s2 $ Just x)) $ Set.toList t2)

specInfoMapBool :: FDSolver s => FDSpecInfoBool s -> Map (FDBoolSpecType s) (FDBoolSpec s)
specInfoMapBool (FDSpecInfoBool { fdspBoolSpec = f, fdspBoolTypes = t }) = Map.fromList $ map (\t -> (t,myFromJust "specInfoMapBool" $ f $ Just t)) $ Set.toList t

specInfoMapInt :: FDSolver s => FDSpecInfoInt s -> Map (FDIntSpecType s) (FDIntSpec s)
specInfoMapInt (FDSpecInfoInt { fdspIntSpec = f, fdspIntTypes = t }) = Map.fromList $ map (\t -> (t,myFromJust "specInfoMapInt" $ f $ Just t)) $ Set.toList t

specInfoMapCol :: FDSolver s => FDSpecInfoCol s -> Map (FDColSpecType s) (FDColSpec s)
specInfoMapCol (FDSpecInfoCol { fdspColSpec = f, fdspColTypes = t }) = Map.fromList $ map (\t -> (t,myFromJust "specInfoMapCol" $ f $ Just t)) $ Set.toList t

specInfoBoolTerm :: FDSolver s => FDBoolTerm s -> s (FDSpecInfoBool s)
specInfoBoolTerm t = do
  let (tp,sp) = fdBoolSpec_term t
  s <- sp
  return $ FDSpecInfoBool { fdspBoolSpec = \t -> case t of { Nothing -> Just s; Just tt | tp==tt -> Just s; _ -> Nothing }, fdspBoolVar = Nothing, fdspBoolVal = Nothing, fdspBoolTypes = Set.singleton tp }

specInfoIntTerm :: FDSolver s => FDIntTerm s -> s (FDSpecInfoInt s)
specInfoIntTerm t = do
  let (tp,sp) = fdIntSpec_term t
  s <- sp
  return $ FDSpecInfoInt { fdspIntSpec = \t -> case t of { Nothing -> Just s; Just tt | tp==tt -> Just s; _ -> Nothing }, fdspIntVar = Nothing, fdspIntVal = Nothing, fdspIntTypes = Set.singleton tp }

instance Show (FDBoolSpec s) => Show (FDSpecInfoBool s) where
  show (FDSpecInfoBool { fdspBoolSpec = f, fdspBoolVar = e, fdspBoolVal = v }) = "FSSpecInfoBool { default:" ++ (show $ f Nothing) ++ ", var:" ++ (show e) ++ ", val:" ++ (show v) ++ "}"
instance Show (FDIntSpec s) => Show (FDSpecInfoInt s) where
  show (FDSpecInfoInt { fdspIntSpec = f, fdspIntVar = e, fdspIntVal = v }) = "FSSpecInfoInt { default:" ++ (show $ f Nothing) ++ ", var:" ++ (show e) ++ ", val:" ++ (show v) ++ "}"
instance Show (FDColSpec s) => Show (FDSpecInfoCol s) where
  show (FDSpecInfoCol { fdspColSpec = f, fdspColVar = e, fdspColVal = v }) = "FSSpecInfoCol { default:" ++ (show $ f Nothing) ++ ", var:" ++ (show e) ++ ", val:" ++ (show v) ++ "}"

type FDSpecInfo s = ([FDSpecInfoBool s],[FDSpecInfoInt s],[FDSpecInfoCol s])

fdSpecInfo_edge :: FDSolver s => EGEdgeId -> FDInstance s (FDSpecInfo s)
fdSpecInfo_edge f = do
  s <- get
  let edge = getJustEdge f s
      intS p = Map.findWithDefault (emptyFDSpecInfoInt p s) p $ fdsIntVars s
      boolS p = Map.findWithDefault (emptyFDSpecInfoBool p s) p $ fdsBoolVars s
      colS p = Map.findWithDefault (emptyFDSpecInfoCol p s) p $ fdsColVars s
--      an m x = case x of
--        Just i -> Map.lookup i m
--        Nothing -> if Map.null m then Nothing else Just $ snd $ Map.findMin m
--      boolX v = FDSpecInfoBool { fdspBoolSpec = an $ boolS v, fdspBoolVar = Just v, fdspBoolVal = getBoolVal_ v s, fdspBoolTypes = Set.fromList $ Map.keys $ boolS v }
--      intX v = FDSpecInfoInt { fdspIntSpec = an $ intS v, fdspIntVar = Just v, fdspIntVal = getIntVal_ v s, fdspIntTypes = Set.fromList $ Map.keys $ intS v }
--      colX v = FDSpecInfoCol { fdspColSpec = an $ colS v, fdspColVar = Just v, fdspColVal = getColVal_ v s, fdspColTypes = Set.fromList $ Map.keys $ colS v }
  return (map boolS $ boolData $ egeLinks edge, map intS $ intData $ egeLinks edge, map colS $ colData $ egeLinks edge)

fdSpecInfo_spec :: FDSolver s => ([Either (FDSpecInfoBool s) (FDBoolSpecType s,FDBoolSpec s)],[Either (FDSpecInfoInt s) (FDIntSpecType s,FDIntSpec s)],[Either (FDSpecInfoCol s) (FDColSpecType s,FDColSpec s)]) -> FDSpecInfo s
fdSpecInfo_spec (b,i,c) = (fdSpecInfo_spec_b b, fdSpecInfo_spec_i i, fdSpecInfo_spec_c c)

fdSpecInfo_spec_b :: FDSolver s => [Either (FDSpecInfoBool s) (FDBoolSpecType s,FDBoolSpec s)] -> [FDSpecInfoBool s]
fdSpecInfo_spec_b b =
  let fb (Right x) = FDSpecInfoBool { fdspBoolSpec = nt x, fdspBoolVar = Nothing, fdspBoolVal = Nothing, fdspBoolTypes = Set.singleton $ fst x }
      fb (Left x) = x
      nt (_,x) Nothing = Just x
      nt (t1,x) (Just t2) | t1==t2 = Just x
      nt _ _ = Nothing
  in (map fb b)

fdSpecInfo_spec_i :: FDSolver s => [Either (FDSpecInfoInt s) (FDIntSpecType s,FDIntSpec s)] -> [FDSpecInfoInt s]
fdSpecInfo_spec_i i =
  let fi (Right x) = FDSpecInfoInt  { fdspIntSpec  = nt x, fdspIntVar  = Nothing, fdspIntVal  = Nothing, fdspIntTypes = Set.singleton $ fst x }
      fi (Left x) = x
      nt (_,x) Nothing = Just x
      nt (t1,x) (Just t2) | t1==t2 = Just x
      nt _ _ = Nothing
  in (map fi i)

fdSpecInfo_spec_c :: FDSolver s => [Either (FDSpecInfoCol s) (FDColSpecType s,FDColSpec s)] -> [FDSpecInfoCol s]
fdSpecInfo_spec_c c =
  let fc (Right x) = FDSpecInfoCol  { fdspColSpec  = nt x, fdspColVar  = Nothing, fdspColVal  = Nothing, fdspColTypes = Set.singleton $ fst x }
      fc (Left x) = x
      nt (_,x) Nothing = Just x
      nt (t1,x) (Just t2) | t1==t2 = Just x
      nt _ _ = Nothing
  in (map fc c)

-- | A solver needs to be an instance of this FDSolver class in order to
-- create an FDInstance around it.
class 
  (
    Solver s, 
    Term s (FDIntTerm s),
    Term s (FDBoolTerm s),
    Eq (FDBoolSpecType s), Ord (FDBoolSpecType s), Enum (FDBoolSpecType s), Bounded (FDBoolSpecType s), Show (FDBoolSpecType s),
    Eq (FDIntSpecType s),  Ord (FDIntSpecType s),  Enum (FDIntSpecType s),  Bounded (FDIntSpecType s), Show (FDIntSpecType s),
    Eq (FDColSpecType s),  Ord (FDColSpecType s),  Enum (FDColSpecType s),  Bounded (FDColSpecType s), Show (FDColSpecType s),
--    Integral (TermBaseType s (FDIntTerm s)), Num (TermBaseType s (FDBoolTerm s)),
    Show (FDIntSpec s), Show (FDColSpec s), Show (FDBoolSpec s)
  ) => FDSolver s where
  -- term types
  type FDIntTerm s    :: *    -- a Term of s, representing Integer variables
  type FDBoolTerm s   :: *    -- a Term of s, representing Bool variables
  -- spec types
  type FDIntSpec s    :: *    -- a type specifying an Integer expression; should at least support constant Integer's and FDIntTerm's
  type FDBoolSpec s   :: *    -- a type specifying a Bool expression; should at least support constant Bool's and FDBoolTerm's
  type FDColSpec s    :: *    -- a type specifying a Integer array expression; should at least support lists of Int's and lists of IntTerm's
  -- spec type type
  type FDIntSpecType s :: *   -- a type specifying the type of an FDIntSpec s, in case there is more than one
  type FDBoolSpecType s :: *  -- a type specifying the type of an FDIntSpec s, in case there is more than one
  type FDColSpecType s :: *   -- a type specifying the type of an FDIntSpec s, in case there is more than one
  

  -- constructors for specifiers
  fdIntSpec_const     :: EGPar         -> (FDIntSpecType s, s (FDIntSpec s))
  fdBoolSpec_const    :: EGBoolPar     -> (FDBoolSpecType s, s (FDBoolSpec s))
  fdColSpec_const     :: EGColPar      -> (FDColSpecType s, s (FDColSpec s))
  fdColSpec_list      :: [FDIntSpec s] -> (FDColSpecType s, s (FDColSpec s))
  fdIntSpec_term      :: FDIntTerm s   -> (FDIntSpecType s, s (FDIntSpec s))
  fdBoolSpec_term     :: FDBoolTerm s  -> (FDBoolSpecType s, s (FDBoolSpec s))
  fdColSpec_size      :: EGPar         -> (FDColSpecType s, s (FDColSpec s))
  fdIntVarSpec        :: FDIntSpec s   -> s (Maybe (FDIntTerm s))
  fdBoolVarSpec       :: FDBoolSpec s  -> s (Maybe (FDBoolTerm s))

  -- function to inform about allowed types for nodes
  fdTypeReqBool :: s (EGEdge -> [(EGVarId,FDBoolSpecTypeSet s)])
  fdTypeReqInt ::  s (EGEdge -> [(EGVarId,FDIntSpecTypeSet s)])
  fdTypeReqCol ::  s (EGEdge -> [(EGVarId,FDColSpecTypeSet s)])
  fdTypeReqBool = return (\(EGEdge { egeLinks = EGTypeData { boolData = l } }) -> map (\x -> (x,Set.fromList [minBound..maxBound])) l)
  fdTypeReqInt = return (\(EGEdge { egeLinks = EGTypeData { intData = l } }) -> map (\x -> (x,Set.fromList [minBound..maxBound])) l)
  fdTypeReqCol = return (\(EGEdge { egeLinks = EGTypeData { colData = l } }) -> map (\x -> (x,Set.fromList [minBound..maxBound])) l)

  fdTypeVarInt :: s (Set (FDIntSpecType s))
  fdTypeVarBool :: s (Set (FDBoolSpecType s))
  fdTypeVarInt = return $ Set.singleton maxBound
  fdTypeVarBool = return $ Set.singleton maxBound

  -- rating functions for specification of terms
  fdSpecify :: Mixin (SpecFn s)
  fdSpecify = mixinId

  -- inspect collections
  fdColInspect :: FDColSpec s -> s [FDIntTerm s]

  -- function to request processing an edge in a graph
  fdProcess :: Mixin (EGConstraintSpec -> FDSpecInfo s -> FDInstance s ())

  -- add equality constraints
  fdEqualBool :: FDBoolSpec s -> FDBoolSpec s -> FDInstance s ()
  fdEqualInt :: FDIntSpec s -> FDIntSpec s -> FDInstance s ()
  fdEqualCol :: FDColSpec s -> FDColSpec s -> FDInstance s ()

  fdConstrainIntTerm :: FDIntTerm s -> Integer -> s (Constraint s)
  fdSplitIntDomain :: FDIntTerm s -> s ([Constraint s],Bool)
  fdSplitBoolDomain :: FDBoolTerm s -> s ([Constraint s],Bool)

fdGetValBool :: (FDSolver s, EnumTerm s (FDBoolTerm s)) => FDBoolSpec s -> s (Maybe (TermBaseType s (FDBoolTerm s)))
fdGetValInt :: (FDSolver s, EnumTerm s (FDIntTerm s)) => FDIntSpec s -> s (Maybe (TermBaseType s (FDIntTerm s)))

fdGetValBool s = fdBoolVarSpec s >>= \x -> case x of
  Just t -> getValue t
  _ -> return Nothing

fdGetValInt s = fdIntVarSpec s >>= \x -> case x of
  Just t -> getValue t
  _ -> return Nothing

type FDBoolSpecTypeSet s = Set (FDBoolSpecType s)
type FDIntSpecTypeSet s = Set (FDIntSpecType s)
type FDColSpecTypeSet s = Set (FDColSpecType s)

fdCombineSpecify :: FDSolver s => SpecFn s -> SpecFn s -> SpecFn s
fdCombineSpecify a b edge = 
  let (a1,a2,a3) = a edge
      (b1,b2,b3) = b edge
      in (a1++b1,a2++b2,a3++b3)

procEdge :: FDSolver s => FDInstance s Bool
procEdge = do
  s <- get
  if (Set.null $ fdsNewEdges s)
    then return False
    else do
      let f = Set.findMin $ fdsNewEdges s
          edge = getJustEdge f s
      debug ("procEdge("++(show f)++")") $ return ()
      info <- fdSpecInfo_edge f
      full_fdProcess (egeCons edge) info
      debug ("procEdge: marking edge "++(show f)) $ return ()
      markEdge f
      s2 <- get
      return $ not $ Set.null $ fdsNewEdges s2

getEdge :: FDSolver s => EGEdgeId -> FDInstance s (Maybe EGEdge)
getEdge id = do
  s <- get
  return $ do
    v <- fdsModel s
    Map.lookup id $ egmEdges v

markEdge :: FDSolver s => EGEdgeId -> FDInstance s ()
markEdge id = do
  s <- get
  debug ("markEdge: "++(show $ id)) $ return ()
  put $ s { fdsNewEdges = Set.delete id $ fdsNewEdges s, fdsDoneEdges = Set.insert id $ fdsDoneEdges s }

sureMaybe :: [Maybe a] -> Maybe [a]
sureMaybe [] = Just []
sureMaybe (Nothing:_) = Nothing
sureMaybe ((Just a):b) = case sureMaybe b of
  Nothing -> Nothing
  Just l -> Just (a:l)

allIntSpec :: FDSolver s => FDInstance s (Set (FDIntSpecType s))
allIntSpec = return $ Set.fromList [minBound..maxBound]

allBoolSpec :: FDSolver s => FDInstance s (Set (FDBoolSpecType s))
allBoolSpec = return $ Set.fromList [minBound..maxBound]

allColSpec :: FDSolver s => FDInstance s (Set (FDColSpecType s))
allColSpec = return $ Set.fromList [minBound..maxBound]

default_fdSpecify :: FDSolver s => SpecFn s
default_fdSpecify edge = case (debug ("default_fdSpecify("++(show edge)++")") edge) of
  EGEdge { egeCons = EGIntValue c, egeLinks = EGTypeData { intData = [v] } } ->
    ([],[(1000,v,True,do
      let (tp, m) = fdIntSpec_const c
      return $ SpecResSpec (tp,m >>= (\x -> return (x, Just c)))
    )],[])
  EGEdge { egeCons = EGBoolValue c, egeLinks = EGTypeData { boolData = [v] } } ->
    ([(1000,v,True,do
      let (tp, m) = fdBoolSpec_const c
      return $ SpecResSpec (tp, m >>= (\x -> return (x, Just c)))
    )],[],[])
  EGEdge { egeCons = EGColValue c, egeLinks = EGTypeData { colData = [v] } } ->
    ([],[],[(990,v,True,do
      let (tp, m) = fdColSpec_const c
      return $ SpecResSpec (tp, m >>= (\x -> return (x, Just c)))
    )])
  EGEdge { egeCons = EGList s, egeLinks = EGTypeData { colData = [c], intData = l } } -> 
    ([],[],[(500,c,True,do
      x <- mapM (\x -> getIntSpec x) l
      case sureMaybe x of
        Nothing -> return SpecResNone
        Just ll -> do
          let (tp, m) = fdColSpec_list ll
          return $ SpecResSpec $ (tp, m >>= (\x -> return (x, Nothing)))
    )])
  EGEdge { egeCons = EGSize, egeLinks = EGTypeData { colData = [c], intData=[s] } } ->
    ([],[],[(250,c,True,do
      ss <- get
      let k = getIntVal_ s ss
      case k of
        Nothing -> return SpecResNone
        Just ll -> do
          let (tp, m) = fdColSpec_size ll
          return $ SpecResSpec $ (tp, m >>= (\x -> return (x, Nothing)))
     )])
  EGEdge { egeCons = EGRange, egeLinks = EGTypeData { colData = [c], intData=[l,h] } } ->
    ([],[],[(250,c,False,do
      ss <- get
      let ll = getIntVal_ l ss
          hh = getIntVal_ h ss
      case (ll,hh) of
        (Just (Const jl), Just (Const jh)) -> do
          let (tp,m) = fdColSpec_size (Const $ jh-jl+1)
          return $ SpecResSpec $ (tp, m >>= (\x -> return (x, Just $ ColList [Const x | x <- [jl..jh]])))
        (Just jl, Just jh) -> do
          let (tp,m) = fdColSpec_size (jh-jl+1)
          return $ SpecResSpec $ (tp, m >>= (\x -> return (x, Nothing)))
        _ -> return SpecResNone
     )])
  _ -> ([],[],[])

default_fdProcess :: FDSolver s => EGConstraintSpec -> FDSpecInfo s -> FDInstance s ()
default_fdProcess cons _ = error $ "Cannot process "++(show cons)

-- | mark all new edges(=constraints) of a model given in graph-form as to-be-processed
initForModel :: FDSolver s => FDInstance s ()
initForModel = do
  s <- get
  let Just model = fdsModel s
  put $ s { 
    fdsNewEdges = Set.difference (Set.union (fdsNewEdges s) $ Set.fromList $ Map.keys $ egmEdges model) $ fdsDoneEdges s
  }

setAlter :: Ord a => a -> Maybe (Set (Set a)) -> Maybe (Set (Set a))
setAlter _ Nothing = Nothing
setAlter typ (Just x) = let f = fl x in if Set.null f then Nothing else Just f
  where fl = Set.filter $ not . Set.member typ

addSpecInt :: FDSolver s => FDIntSpecType s -> (FDIntSpec s, Maybe EGPar) -> EGVarId -> FDState s -> Maybe (FDSpecInfoInt s) -> Maybe (FDSpecInfoInt s)
addSpecInt tp def id s Nothing = addSpecInt tp def id s (Just $ emptyFDSpecInfoInt id s)
addSpecInt tp (def,val) _ _ (Just (m@(FDSpecInfoInt { fdspIntSpec = f, fdspIntTypes = t }))) =
  Just $ m { 
    fdspIntSpec = \x -> case x of
      Just tt | tt==tp -> Just $ def
      Nothing -> case f Nothing of
        Nothing -> Just def
        Just ttt -> Just ttt
      k -> f k,
    fdspIntTypes = Set.insert tp t,
    fdspIntVal = case val of
      Nothing -> fdspIntVal m
      _ -> val
  }

addSpecBool :: FDSolver s => FDBoolSpecType s -> (FDBoolSpec s, Maybe EGBoolPar) -> EGVarId -> FDState s -> Maybe (FDSpecInfoBool s) -> Maybe (FDSpecInfoBool s)
addSpecBool tp def id s Nothing = addSpecBool tp def id s (Just $ emptyFDSpecInfoBool id s)
addSpecBool tp (def,val) _ _ (Just (m@(FDSpecInfoBool { fdspBoolSpec = f, fdspBoolTypes = t }))) = 
  Just $ m { 
    fdspBoolSpec = \x -> case x of
      Just tt | tt==tp -> Just $ def
      Nothing -> case f Nothing of
        Nothing -> Just def
        Just ttt -> Just ttt
      k -> f k,
    fdspBoolTypes = Set.insert tp t,
    fdspBoolVal = case val of
      Nothing -> fdspBoolVal m
      _ -> val
  }

addSpecCol :: FDSolver s => FDColSpecType s -> (FDColSpec s, Maybe EGColPar) -> EGVarId -> FDState s -> Maybe (FDSpecInfoCol s) -> Maybe (FDSpecInfoCol s)
addSpecCol tp def id s Nothing = addSpecCol tp def id s (Just $ emptyFDSpecInfoCol id s)
addSpecCol tp (def,val) _ _ (Just (m@(FDSpecInfoCol { fdspColSpec = f, fdspColTypes = t }))) = 
  Just $ m {
    fdspColSpec = \x -> case x of
      Just tt | tt==tp -> Just $ def
      Nothing -> case f Nothing of
        Nothing -> Just def
        Just ttt -> Just ttt
      k -> f k,
    fdspColTypes = Set.insert tp t,
    fdspColVal = case val of
      Nothing -> fdspColVal m
      _ -> val
  }

-- | add an int term
addIntVar :: FDSolver s => EGVarId -> FDIntSpecType s -> (FDIntSpec s, Maybe EGPar) -> FDInstance s ()
addIntVar id typ (spec@(rs,_)) = do
--  debug ("addIntVar id="++(show id)++" typ="++(show typ)++" spec="++(show spec)) $ return ()
  s <- get
  case (Map.lookup id $ fdsIntVars s) of
    Just t | not (Set.null $ fdspIntTypes t) -> case (fdspIntSpec t Nothing) of
      Just x -> fdEqualInt rs x
      Nothing -> case fdspIntSpec t $ Just $ Set.findMax $ fdspIntTypes t of
        Just x -> fdEqualInt rs x
        Nothing -> return ()
    _ -> return ()
  s2 <- get
  put $ s2
    {
      fdsIntVars = Map.alter (addSpecInt typ spec id s2) id $ fdsIntVars s2,
      fdsIntVarBusy = Set.delete id $ fdsIntVarBusy s2,
      fdsIntVarTypes = Map.alter (setAlter typ) id $ fdsIntVarTypes s2
    }

-- | add a bool term
addBoolVar :: FDSolver s => EGVarId -> FDBoolSpecType s -> (FDBoolSpec s, Maybe EGBoolPar) -> FDInstance s ()
addBoolVar id typ (spec@(rs,_)) = do
--  debug ("addBoolVar id="++(show id)++" typ="++(show typ)++" spec="++(show spec)) $ return ()
  s <- get
  case (Map.lookup id $ fdsBoolVars s) of
    Just t | not (Set.null $ fdspBoolTypes t) -> case (fdspBoolSpec t Nothing) of
      Just x -> fdEqualBool rs x
      Nothing -> case fdspBoolSpec t $ Just $ Set.findMax $ fdspBoolTypes t of
        Just x -> fdEqualBool rs x
        Nothing -> return ()
    _ -> return ()
  s2 <- get
  put $ s2
    { 
      fdsBoolVars = Map.alter (addSpecBool typ spec id s2) id $ fdsBoolVars s2,
      fdsBoolVarBusy = Set.delete id $ fdsBoolVarBusy s2,
      fdsBoolVarTypes = Map.alter (setAlter typ) id $ fdsBoolVarTypes s2
    }

-- | add a col term
addColVar :: FDSolver s => EGVarId -> FDColSpecType s -> (FDColSpec s, Maybe EGColPar) -> FDInstance s ()
addColVar id typ (spec@(rs,_)) = do
--  debug ("addColVar id="++(show id)++" typ="++(show typ)++" spec="++(show spec)) $ return ()
  s <- get
  case (Map.lookup id $ fdsColVars s) of
    Just t | not (Set.null $ fdspColTypes t) -> case (fdspColSpec t Nothing) of
      Just x -> fdEqualCol rs x
      Nothing -> case fdspColSpec t $ Just $ Set.findMax $ fdspColTypes t of
        Just x -> fdEqualCol rs x
        Nothing -> return ()
    _ -> return ()
  s2 <- get
  put $ s2
    { 
      fdsColVars = Map.alter (addSpecCol typ spec id s2) id $ fdsColVars s2,
      fdsColVarBusy = Set.delete id $ fdsColVarBusy s2,
      fdsColVarTypes = Map.alter (setAlter typ) id $ fdsColVarTypes s2
    }

full_fdProcess :: FDSolver s => EGConstraintSpec -> FDSpecInfo s -> FDInstance s ()
full_fdProcess = mixin (fdProcess <@> mixinLift default_fdProcess)

full_fdSpecify :: FDSolver s => SpecFn s
full_fdSpecify = mixin (fdSpecify <@> mixinLift default_fdSpecify)


getJustEdge :: FDSolver s => EGEdgeId -> FDState s -> EGEdge
getJustEdge i s = 
  let Just m = fdsModel s
      Just x = Map.lookup i (egmEdges m)
      in x

buildSpecDb :: FDSolver s => FDInstance s ()
buildSpecDb = do
  s <- get
  let origDb = fdsDb s
      ne = debug "bsdb: ne" $ map (\k -> (k,getJustEdge k s)) $ Set.toList $ debug "bsbd: fdsne" $ fdsNewEdges s
      proc db (eid,edge) = do 
        let (lB,lI,lC) = debug ("bsbd: specify("++(show edge)++")") $ full_fdSpecify edge
            dB = foldr (\(prio,var,full,spec) d -> debug "bsbd: addbool" $ addBoolSpec d (prio,var,if full then Just eid else Nothing,spec)) db $ debug ("lB["++(show $ length lB)++"]") lB
            dI = foldr (\(prio,var,full,spec) d -> debug "bsbd: addint" $ addIntSpec d (prio,var,if full then Just eid else Nothing,spec)) dB $ debug ("lI["++(show $ length lI)++"]") lI
            dC = foldr (\(prio,var,full,spec) d -> debug "bsbd: addcol" $ addColSpec d (prio,var,if full then Just eid else Nothing,spec)) dI $ debug ("lC["++(show $ length lC)++"]") lC
            in dC
      newDb = foldl proc origDb ne
  put $ s { fdsDb = newDb }

addBoolTypeReq :: FDSolver s => EGVarId -> FDBoolSpecTypeSet s -> FDInstance s ()
addBoolTypeReq var set = do
  s <- get
  let chk tp = case Map.lookup var (fdsBoolVars s) of
            Nothing -> False
            Just x -> Set.member tp (fdspBoolTypes x)
      sset = Map.findWithDefault Set.empty var (fdsBoolVarTypes s)
  if Set.member set sset
    then return ()
    else if any chk (Set.toList set)
      then return ()
      else do
        let nsset = Set.insert set sset
        put $ s 
          { 
            fdsBoolVarTypes = Map.insert var nsset $ fdsBoolVarTypes s
          }

addIntTypeReq :: FDSolver s => EGVarId -> FDIntSpecTypeSet s -> FDInstance s ()
addIntTypeReq var set = do
  s <- get
  let chk tp = case Map.lookup var (fdsIntVars s) of
            Nothing -> False
            Just x -> Set.member tp (fdspIntTypes x)
      sset = Map.findWithDefault Set.empty var (fdsIntVarTypes s)
  if Set.member set sset
    then return ()
    else if any chk (Set.toList set)
      then return ()
      else do
        let nsset = Set.insert set sset
        put $ s 
          { 
            fdsIntVarTypes = Map.insert var nsset $ fdsIntVarTypes s
          }

addColTypeReq :: FDSolver s => EGVarId -> FDColSpecTypeSet s -> FDInstance s ()
addColTypeReq var set = do
  s <- get
  let chk tp = case Map.lookup var (fdsColVars s) of
            Nothing -> False
            Just x  -> Set.member tp (fdspColTypes x)
      sset = Map.findWithDefault Set.empty var (fdsColVarTypes s)
  if Set.member set sset
    then return ()
    else if any chk (Set.toList set)
      then return ()
      else do
        let nsset = Set.insert set sset
        put $ s 
          {
            fdsColVarTypes = Map.insert var nsset (fdsColVarTypes s)
          }

addTypeReqs :: FDSolver s => FDInstance s ()
addTypeReqs = do
  s <- get
  fBool <- liftFD fdTypeReqBool
  fInt  <- liftFD fdTypeReqInt
  fCol  <- liftFD fdTypeReqCol
  let ne = map (\k -> getJustEdge k s) $ Set.toList $ fdsNewEdges s
      proc edge = do
        mapM_ (uncurry addBoolTypeReq) $ fBool edge
        mapM_ (uncurry addIntTypeReq) $ fInt edge
        mapM_ (uncurry addColTypeReq) $ fCol edge
  mapM_ proc ne

processEx :: FDSolver s => Bool -> FDInstance s ()
processEx x = do
        ssm1 <- get
        let ss0 = ssm1 { fdsModel = Just $ pruneNodes $ myFromJust "processEx" $ fdsModel ssm1 }
        debug ("process ["++(show $ fdsLevel ss0)++"]") $ return ()
        -- search spec type requirements for all to-be-processed edges
        debug ("addTypeReqs ["++(show $ fdsLevel ss0)++"]") $ addTypeReqs
        -- optimize type requirements
        debug ("optimizeVarTypes["++(show $ fdsLevel ss0)++"]") $ optimizeVarTypes
        ss <- get
        debug ("DUMP type reqs ["++(show $ fdsLevel ss0)++"]: "++(show $ fdsIntVarTypes ss)) $ return ()
        -- build specifier database for all to-be-processed edges
        debug ("buildSpecDb ["++(show $ fdsLevel ss0)++"]") $ buildSpecDb
        ss2 <- get
        debug ("DUMP spec db ["++(show $ fdsLevel ss0)++"]: "++(show $ fdsDb ss2)) $ return ()
        -- create as much specifiers as possible (marking consumed edges as processed)
        whileM_ $ debug ("decompBest ["++(show $ fdsLevel ss0)++"]") decompBest
        -- try default specifier for remaining boolean nodes (=create new underlying term for each)
        whileM_ $ debug ("decompDefBool ["++(show $ fdsLevel ss0)++"]") decompDefaultBool
        -- try default specifier for remaining integer nodes (=create new underlying term for each)
        whileM_ $ debug ("decompDefInt ["++(show $ fdsLevel ss0)++"]") decompDefaultInt
        ss3 <- get
        debug ("DUMP specs: "++(dumpSpec ss3)) $ return ()
        -- process remaining edges
        if x
          then whileM_ $ debug ("procEdge ["++(show $ fdsLevel ss0)++"]") procEdge
          else return ()

process :: FDSolver s => FDInstance s ()
process = processEx True

commit :: FDSolver s => FDInstance s ()
commit = do
  s <- get
  debug "begin commit" $ return ()
  case (fdsExpr s,fdsForceBool s,fdsForceInt s,fdsForceCol s) of
      (BoolConst True,[],[],[]) -> return ()
      (expr,_,_,_) -> do
        debug ("expr=["++(show expr)++"]") $ return ()
        let (dcd,graph,vars) = debug "decomposing" $ decomposeEx (fdsDecomp s) (fdsVars s) expr (fdsForceBool s,fdsForceInt s,fdsForceCol s) $ fdsModel s
        put $ s { fdsExpr = BoolConst True, fdsDecomp = dcd, fdsModel = Just graph, fdsForceBool=[], fdsForceInt=[], fdsForceCol=[], fdsVars = max vars (fdsVars s) }
        debug ("graph=["++(present graph)++"]"++"]") $ return ()
        -- mark all non-yet-processed edges as to-be-processed
        debug "initForModel" $ initForModel
        process

instance FDSolver s => Solver (FDInstance s) where
  type Constraint (FDInstance s) = Either Model (Constraint s)
  type Label (FDInstance s) = FDLabel s
  add (Left expr) = do
    s <- get
    if (fdsFailed s)
      then return False
      else do
        put $ s { fdsExpr = (fdsExpr s) @&& expr }
        return True
  add (Right col) = do
    s <- get
    if (fdsFailed s)
      then return False
      else do
        ret <- liftFD $ add col
        if ret
          then return True
          else do
            setFailed
            return False
  mark = do
    commit
    ss <- get
    sl <- liftFD mark
    return $ FDLabel { fdlState=ss, fdlLabel=sl }
  markn n = do
    commit
    ss <- get
    sl <- liftFD $ markn n
    return $ FDLabel { fdlState=ss, fdlLabel=sl }
  goto label = do
    liftFD $ goto $ fdlLabel label
    put $ fdlState label
  run x = run $ runFD x

instance FDSolver s => Term (FDInstance s) ModelInt where
  newvar = do
    s <- get
    let i = fdsVars s
    put $ s { fdsVars = 1+i }
    return $ Term $ ModelIntVar i
  type Help (FDInstance s) ModelInt = ()
  help _ _ = ()

instance FDSolver s => Term (FDInstance s) ModelBool where
  newvar = do
    s <- get
    let i = fdsVars s
    put $ s { fdsVars = 1+i }
    return $ BoolTerm $ ModelBoolVar i
  type Help (FDInstance s) ModelBool = ()
  help _ _ = ()

instance FDSolver s => Term (FDInstance s) ModelCol where
  newvar = do
    s <- get
    let i = fdsVars s
    put $ s { fdsVars = 1+i }
    return $ ColTerm $ ModelColVar i
  type Help (FDInstance s) ModelCol = ()
  help _ _ = ()

newCol :: FDSolver s => FDInstance s ModelCol
newCol = newvar

newInt :: FDSolver s => FDInstance s ModelInt
newInt = newvar

newBool :: FDSolver s => FDInstance s ModelBool
newBool = newvar

combine :: [Maybe a] -> [a] -> [a]
combine [] _ = []
combine (Nothing:r) (a:b) = a:(combine r b)
combine (Just x:r) b = x:(combine r b)

realGetIntTerm :: FDSolver s => [ModelInt] -> FDInstance s [FDIntTerm s]
realGetIntTerm m = do
  s <- debug ("realGetIntTerm: "++(show m)) $ get
  put $ s { fdsForceInt = m++(fdsForceInt s) }
  commit
  s2 <- get
  let ids = map (\x -> decompIntLookup (fdsDecomp s2) x) m
  tp <- liftFD $ fdTypeVarInt
  specs <- mapM (\(Just id) -> getIntSpec_ id tp) ids
  vars <- mapM (\(Just (_,spec)) -> liftFD $ fdIntVarSpec spec) specs
  let rvars = map (\(Just x) -> x) vars
  s3 <- get
  put $ s3 { fdsForcedInt = Map.union (fdsForcedInt s3) (Map.fromList $ zip m rvars) }
  return rvars

getSingleIntTerm :: FDSolver s => ModelInt -> FDInstance s (FDIntTerm s)
getSingleIntTerm m = do
  s <- get
  case Map.lookup m (fdsForcedInt s) of
    Nothing -> realGetIntTerm [m] >>= return.head
    Just d -> return d

getIntTerm :: FDSolver s => [ModelInt] -> FDInstance s [FDIntTerm s]
getIntTerm m = do
  s <- get
  let lo = map (\x -> (x,Map.lookup x $ fdsForcedInt s)) m
  let go = map fst $ filter (\(_,x) -> isNothing x) lo
  vo <- case go of
    [] -> return []
    _ -> realGetIntTerm go
  return $ combine (map snd lo) vo

realGetBoolTerm :: FDSolver s => [ModelBool] -> FDInstance s [FDBoolTerm s]
realGetBoolTerm m = do
  s <- get
  put $ s { fdsForceBool = m++(fdsForceBool s) }
  commit
  s2 <- get
  let ids = map (\x -> decompBoolLookup (fdsDecomp s2) x) m
  tp <- liftFD $ fdTypeVarBool
  specs <- mapM (\(Just id) -> getBoolSpec_ id tp) ids
  vars <- mapM (\(Just (_,spec)) -> liftFD $ fdBoolVarSpec spec) specs
  let rvars = map (\(Just x) -> x) vars
  s3 <- get
  put $ s3 { fdsForcedBool = Map.union (fdsForcedBool s3) (Map.fromList $ zip m rvars) }
  return rvars

getBoolTerm :: FDSolver s => [ModelBool] -> FDInstance s [FDBoolTerm s]
getBoolTerm m = do
  s <- get
  let lo = map (\x -> (x,Map.lookup x $ fdsForcedBool s)) m
  let go = map fst $ filter (\(_,x) -> isNothing x) lo
  vo <- case go of
    [] -> return []
    _ -> realGetBoolTerm go
  return $ combine (map snd lo) vo

getColTerm :: FDSolver s => [ModelCol] -> FDColSpecType s -> FDInstance s [FDColSpec s]
getColTerm m tp = do
  s <- get
  put $ s { fdsForceCol = m++(fdsForceCol s) }
  commit
  s2 <- get
  let ids = map (\x -> decompColLookup (fdsDecomp s2) x) m
  specs <- mapM (\(Just id) -> getColSpec_ id (Set.singleton tp)) ids
  return $ map (snd . myFromJust ("getColTerm(tp="++(show tp)++")")) specs

getColItems :: FDSolver s => ModelCol -> FDColSpecType s -> FDInstance s [FDIntTerm s]
getColItems c tp = do
  [cc] <- getColTerm [c] tp
  lst <- liftFD $ fdColInspect cc
  return lst

instance (FDSolver s, EnumTerm s (FDIntTerm s)) => EnumTerm (FDInstance s) ModelInt where
  type TermBaseType (FDInstance s) ModelInt = TermBaseType s (FDIntTerm s)
  getDomainSize v = do
    f <- getFailed
    if f 
      then return 0
      else do
        var <- getSingleIntTerm v
        liftFD $ getDomainSize var
  getValue v = do
    var <- getSingleIntTerm v
    liftFD $ getValue var
--  setValue var val = return [var @== cte val]
  setValue _ = error "setting of boolean variable through FD interface is not implemented"
  getDomain var = error "retrieval of full domain not implemented in FD"
  splitDomain v = do
    var <- getSingleIntTerm v
    (doms,full) <- liftFD $ fdSplitIntDomain var
    return (map (\x -> [Right x]) doms, full)
  enumerator = case enumerator of
    Nothing -> Nothing
    Just e -> Just $ \l -> label $ do
      f <- getFailed
      if f
        then return false
        else do
          ll <- getIntTerm l
          return $ liftFDTree $ e ll

instance (FDSolver s, EnumTerm s (FDBoolTerm s)) => EnumTerm (FDInstance s) ModelBool where
  type TermBaseType (FDInstance s) ModelBool = TermBaseType s (FDBoolTerm s)
  getDomainSize v = do
    f <- getFailed
    if f
      then return 0
      else do
        [var] <- getBoolTerm [v]
        liftFD $ getDomainSize var
  getValue v = do
    [var] <- getBoolTerm [v]
    liftFD $ getValue var
--  setValue var val = return [var @= BoolConst (val /]
  setValue _ = error "setting of boolean variable through FD interface is not implemented"
  getDomain var = error "retrieval of full boolean domain not implemented in FD"
  splitDomain v = do
    [var] <- getBoolTerm [v]
    (doms,full) <- liftFD $ fdSplitBoolDomain var
    return (map (\x -> [Right x]) doms, full)
  enumerator = case enumerator of
    Nothing -> Nothing
    Just e -> Just $ \l -> label $ do
      f <- getFailed
      if f
        then return false
        else do
          ll <- getBoolTerm l
          return $ liftFDTree $ e ll

getIntVal_ :: FDSolver s => EGVarId -> FDState s -> Maybe EGPar
getIntVal_ id s =
  let r1 = 
        case Map.lookup id (fdsIntVars s) of
          Nothing -> Nothing
          Just x -> fdspIntVal x
      in case r1 of
        Nothing ->
          let Just j = fdsModel s
              ei = findEdge j EGIntType id (==0) (\x -> case x of { EGIntValue _ -> True; _ -> False })
              in case ei of
                Nothing -> Nothing
                Just (_,ed) -> case egeCons ed of { EGIntValue c -> Just c }
        Just x -> r1

getIntVal :: FDSolver s => EGVarId -> FDInstance s (Maybe EGPar)
getIntVal id = gets $ getIntVal_ id

getBoolVal_ :: FDSolver s => EGVarId -> FDState s -> Maybe EGBoolPar
getBoolVal_ id s =
  let r1 = 
        case Map.lookup id (fdsBoolVars s) of
          Nothing -> Nothing
          Just x -> fdspBoolVal x
      in case r1 of
        Nothing ->
          let Just j = fdsModel s
              l = getConnectedEdges j EGBoolType id
              f (EGEdge { egeCons = EGBoolValue c },_) _ = Just c
              f _ s = s
              in foldr f Nothing l
        Just x -> r1

getBoolVal :: FDSolver s => EGVarId -> FDInstance s (Maybe EGBoolPar)
getBoolVal id = gets $ getBoolVal_ id

getColVal_ :: FDSolver s => EGVarId -> FDState s -> Maybe EGColPar
getColVal_ id s =
  let r1 = 
        case Map.lookup id (fdsColVars s) of
          Nothing -> Nothing
          Just x -> fdspColVal x
      in case r1 of
        Nothing ->
          let Just j = fdsModel s
              l = getConnectedEdges j EGColType id
              f (EGEdge { egeCons = EGColValue c },_) _ = Just c
              f _ s = s
              in foldr f Nothing l
        Just x -> r1

getColVal :: FDSolver s => EGVarId -> FDInstance s (Maybe EGColPar)
getColVal id = gets $ getColVal_ id

setFailed :: FDSolver s => FDInstance s ()
setFailed = do 
  s <- get
  debug "setFailed!" $ return ()
  put $ s { fdsFailed = True }

getFailed :: FDSolver s => FDInstance s Bool
getFailed = do
  s <- get
  return $ fdsFailed s

addFD :: (Show (Constraint s), FDSolver s) => Constraint s -> FDInstance s ()
addFD c = do
  s <- get
  if (fdsFailed s)
    then debug ("addFD("++(show c)++"): already failed") $ return ()
    else do
      x <- liftFD $ add c
      debug ("addFD("++(show c)++"): result="++(show x)) $ return ()
      if not x then setFailed else return ()

getDefIntSpec :: FDSolver s => FDSpecInfoInt s -> FDIntSpec s
getDefIntSpec (FDSpecInfoInt { fdspIntSpec = f }) = case f Nothing of
  Just t -> t
  Nothing -> error "getDefIntSpec: no spec"

getDefBoolSpec :: FDSolver s => FDSpecInfoBool s -> FDBoolSpec s
getDefBoolSpec (FDSpecInfoBool { fdspBoolSpec = f }) = case f Nothing of
  Just t -> t
  Nothing -> error "getDefBoolSpec: no spec"

getDefColSpec :: FDSolver s => FDSpecInfoCol s -> FDColSpec s
getDefColSpec (FDSpecInfoCol { fdspColSpec = f }) = case f Nothing of
  Just t -> t
  Nothing -> error "getDefColSpec: no spec"

-- getFullIntSpec :: FDSolver s => EGVarId -> s (FDSpecInfoInt s)
getFullIntSpec id = do
  s <- get
  return $ myFromJust "getFullIntSpec" $ Map.lookup id $ fdsIntVars s

-- getFullBoolSpec :: FDSolver s => EGVarId -> s (FDSpecInfoBool s)
getFullBoolSpec id = do
  s <- get
  return $ myFromJust "getFullBoolSpec" $ Map.lookup id $ fdsBoolVars s

-- getFullColSpec :: FDSolver s => EGVarId -> s (FDSpecInfoCol s)
getFullColSpec id = do
  s <- get
  return $ myFromJust "getFullColSpec" $ Map.lookup id $ fdsColVars s

fdNewvar :: (FDSolver s, Term s t) => FDInstance s (Maybe t)
fdNewvar = do
  s <- get
  if fdsDummyLevel s > 0
    then return Nothing
    else liftFD newvar >>= return . Just
