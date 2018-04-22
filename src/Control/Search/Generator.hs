{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Search.Generator
  ( (<@>)
  , mmap
  , search
  , ($==)
  , ($/=)
  , ($<) 
  , ($<=)
  , ($>) 
  , ($>=)
  , (@>)
  , VarId(..)

  , mapE, Eval(..), inite, seqSwitch, VarInfoM(..), MkEval, Evalable
  , SeqPos(..), Search(..), (@.), (@$), (@>>>@)
  , ref_count, ref_countx, ref_count_type, commentEval, (@++@)
  , entry, numSwitch, SearchCombiner(..)
  , buildCombiner, extractCombiners
  , memo
  , memoLoop {- ,MemoWrapper, runMemoWrapper-}
  , rReaderT
#ifndef NOMEMO
  , cacheStatement
#endif
  , cloneBase
  , mkCopy, mkUpdate, rp, inits, mseqs
  , cachedCommit, cachedAbort, cachedClone
  , nextSame, nextDiff, pushLeft, pushRight, bodyE, addE, returnE, initE, failE, tryE, startTryE, tryE_, deleteE
  ) where

import Debug.Trace

import Text.PrettyPrint hiding (space)
import Data.List (sort, nub, sortBy)
import Data.List (intercalate)
import Data.Unique
import Unsafe.Coerce

import Control.Search.Language
import Control.Search.GeneratorInfo
#ifndef NOMEMO
import Control.Search.Memo
import Control.Search.MemoReader
#endif

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)
import Control.Monatron.MonadInfo
import Control.Monatron.IdT

import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Search.SStateT

modify :: StateM s f => (s -> s) -> f ()
modify f = get >>= put . f

newtype GenModeT m a = GenModeT { unGenModeT :: ReaderT GenMode m a }
  deriving (MonadT, ReaderM GenMode, FMonadT)

class Monad m => GenModeM m where
  getFlags :: m PrettyFlags
  getMode :: m GenMode
  getFlags = getMode >>= return . PrettyFlags

instance MonadInfoT GenModeT where
  tminfo x = miInc "GenModeT" $ minfo (runReaderT undefined (unGenModeT x))

instance Monad m => GenModeM (GenModeT m) where
  getMode = GenModeT ask

instance (GenModeM m, FMonadT t) => GenModeM (t m) where
  getMode = lift getMode

runGenModeT :: GenMode -> GenModeT m a -> m a
runGenModeT m (GenModeT r) = runReaderT m r

type TreeState = Value

newtype VarId = VarId Int
  deriving (Ord, Eq, Show)

type VarInfo = Map VarId Info

newtype VarInfoT m a = VarInfoT { unVarInfoT :: SStateT VarInfo m a }
  deriving (MonadT,StateM VarInfo, FMonadT)

instance MonadInfoT VarInfoT where
  tminfo x = miInc "VarInfoT" $ minfo (runSStateT undefined (unVarInfoT x))

class Monad m => VarInfoM m where
  lookupVarInfo :: VarId -> m Info
  setVarInfo :: VarId -> Info -> m ()

instance Monad m => VarInfoM (VarInfoT m) where
  lookupVarInfo var = VarInfoT $ get >>= return . fromJust . Map.lookup var
  setVarInfo var val = VarInfoT $ get >>= \tbl -> (put $ Map.insert var val tbl)

instance (VarInfoM m, FMonadT t) => VarInfoM (t m) where
  lookupVarInfo = lift . lookupVarInfo
  setVarInfo var val = lift (setVarInfo var val)

#ifdef NOMEMO
class (VarInfoM m, HookStatsM m, MonadInfo m, GenModeM m, Functor m) => Evalable m
instance (VarInfoM m, HookStatsM m, MonadInfo m, GenModeM m, Functor m) => Evalable m
#else
class (VarInfoM m, HookStatsM m, MonadInfo m, MemoM m, GenModeM m, Functor m) => Evalable m
instance (VarInfoM m, HookStatsM m, MonadInfo m, MemoM m, GenModeM m, Functor m) => Evalable m
#endif

data Eval m = Eval 
                 { structs    :: ([Struct],[Struct])                        -- auxiliary type declarations
                 , treeState_ :: [(String,Type, Info -> m Statement)]        -- tree state fields (name, type, init)
                 , evalState_  :: [(String,Type, Info -> m Value)]
         , nextSameH   :: Info -> m Statement
         , nextDiffH   :: Info -> m Statement
                 , pushLeftH   :: Info -> m Statement
                 , pushRightH  :: Info -> m Statement
         , bodyH      :: Info -> m Statement
                 , initH      :: Info -> m Statement
                 , addH       :: Info -> m Statement
         , returnH    :: Info -> m Statement
             , failH      :: Info -> m Statement
                 , tryH       :: Info -> m Statement
                 , tryLH      :: Info -> m Statement
                 , startTryH  :: Info -> m Statement
                 , intArraysE :: [String]
                 , boolArraysE :: [String]
                 , intVarsE   :: [String]
          , -- Free heap allocated memory for search heuristic associated to this node
           -- because it is being abandoned.
           --
           -- BE CAREFUL: deallocate memory only once in case of multiple references.
           --
           -- Example use case: untilLoop
           deleteH    :: Info -> m Statement
                 , toString   :: String
                 , canBranch  :: m Bool
                 , complete   :: Info -> m Value
                 }

commentStatement :: (HookStatsM m) => String -> Eval m -> (Info -> m Statement) -> (Info -> m Statement)
#ifdef OUTPUTCOMMENTS
commentStatement c e f = \x -> (f x >>= \s -> return (DebugOutput ("begin: " ++ c ++ " @ " ++ toString e) >>> s >>> DebugOutput ("end:   " ++ c ++ " @ " ++ toString e)))
#else 
commentStatement c e f = \x -> (f x >>= \s -> return (comment ("begin: " ++ c ++ " @ " ++ toString e) >>> s >>> comment ("end:   " ++ c ++ " @ " ++ toString e)))
#endif

commentEval :: Evalable m => Eval m -> Eval m
#ifdef COMMENTS
commentEval e = 
          e    { treeState_ = map (\(a,b,c) -> (a,b,commentStatement "treeState" e c)) (treeState_ e)
               , nextSameH = commentStatement "nextSame" e (nextSame e)
               , nextDiffH = commentStatement "nextDiff" e (nextDiff e)
               , pushLeftH = commentStatement "pushLeft" e (pushLeft e)
               , pushRightH = commentStatement "pushRight" e (pushRight e)
               , bodyH = commentStatement "bodyE" e (bodyE e)
               , initH = commentStatement "initE" e (initE e)
               , addH = commentStatement "addE" e (addE e)
               , returnH = commentStatement "returnE" e (returnE e)
               , failH = commentStatement "failE" e (failE e)
               , tryH = commentStatement "tryE" e (tryE e)
               , tryLH = commentStatement "tryE_" e (tryE_ e)
               , deleteH = commentStatement "deleteE" e (deleteE e)
               , startTryH = commentStatement "startTryE" e (startTryE e)
               }
#else
commentEval = id
#endif

entry :: Monad m => (String,Type,Value -> Statement) -> (String,Type,Info -> m Statement)
entry (name,ty,up) = (name, ty, \i -> return (up $ (@->name) $ tstate i))

rootEntry :: Monad m => [(String,Type,Info -> m Statement)]
rootEntry = [ entry ("space",Pointer SpaceType,assign RootSpace)
            ]

inits :: Evalable m => Eval m -> Info -> m Statement
inits e i = initTreeState_ i e @>>>@ initH e i

inite :: Monad m => [(String,Info -> m Value)] -> Info -> m Statement
inite fs i = mseqs [init i >>= \ini -> return (estate i @=> f <== ini) | (f,init) <- fs]

mkCopy   i f   = (tstate i @-> f) <==   (tstate (old i) @-> f)
mkUpdate i f g = (tstate i @-> f) <== g (tstate (old i) @-> f)

mseqs lst = sequence lst >>= \s -> return (seqs s)

mapE :: (HookStatsM m, HookStatsM n) => (forall x. m x -> n x) -> Eval m -> Eval n
mapE x = mapE_ (const x)

data HookStat = HookStat { nCalls :: Integer }

newtype HookStatsT m a = HookStatsT { unHookStatsT :: StateT HookStat m a }
  deriving (Monad, StateM HookStat, FMonadT, MonadT)

runHookStatsT :: Monad m => HookStatsT m a -> m (a, Integer)
runHookStatsT m = do
  (a, s) <- runStateT (HookStat { nCalls = 0 }) $ unHookStatsT m
  return (a, nCalls s)

instance MonadInfoT HookStatsT where
  tminfo = miInc "HookStatsT" . minfo . runHookStatsT

class Monad m => HookStatsM m where
  hookCalled :: m ()

instance Monad m => HookStatsM (HookStatsT m) where
  hookCalled = modify (\st -> st { nCalls = 1 + nCalls st })

instance (MonadT t, HookStatsM m) => HookStatsM (t m) where
  hookCalled = lift hookCalled

callHook :: HookStatsM m => String -> Eval m -> Info -> m ()
callHook s e i = hookCalled

nextSame, nextDiff, pushLeft, pushRight, bodyE, addE, returnE, initE, failE, tryE, startTryE, tryE_, deleteE :: HookStatsM m => Eval m -> Info -> m Statement
nextSame e i = callHook "nextSame" e i >> nextSameH e i
nextDiff e i = callHook "nextDiff" e i >> nextDiffH e i
pushLeft e i = callHook "pushLeft" e i  >> pushLeftH e i
pushRight e i = callHook "pushRight" e i  >> pushRightH e i
bodyE e i = callHook "body" e i  >> bodyH e i
addE e i = callHook "add" e i  >> addH e i
returnE e i = callHook "return" e i  >> returnH e i
initE e i = callHook "init" e i >> initH e i
failE e i = callHook "fail" e i >> failH e i
tryE e i = callHook "try" e i >> tryH e i
startTryE e i = callHook "startTry" e i  >> startTryH e i
tryE_ e i = callHook "tryL" e i  >> tryLH e i
deleteE e i = callHook "deleteH" e i  >> deleteH e i

mapE_ :: (HookStatsM m, HookStatsM n) => (forall x. Maybe Info -> m x -> n x) -> Eval m -> Eval n
mapE_ f e =
  Eval { structs    = structs e
       , treeState_  = map (\(s,t,m) -> (s,t,\i -> f (Just i) (m i))) (treeState_ e)
       , evalState_ = map (\(s,t,m) -> (s,t,\i -> f (Just i) (m i))) (evalState_ e)
       , nextSameH  = \i -> f (Just i) (nextSame e i)
       , nextDiffH  = \i -> f (Just i) (nextDiff e i)
       , pushLeftH  = \i -> f (Just i) (pushLeft e i)
       , pushRightH = \i -> f (Just i) (pushRight e i)
       , bodyH      = \i -> f (Just i) (bodyE e i)
       , addH       = \i -> f (Just i) (addE e i)
       , returnH    = \i -> f (Just i) (returnE e i)
       , initH      = \i -> f (Just i) (initE e i)
       , failH      = \i -> f (Just i) (failE e i)
       , tryH       = \i -> f (Just i) (tryE e i)
       , startTryH  = \i -> f (Just i) (startTryE e i)
       , tryLH      = \i -> f (Just i) (tryE_ e i)
       , boolArraysE = boolArraysE e
       , intArraysE = intArraysE e
       , intVarsE   = intVarsE e
       , deleteH    = \i -> f (Just i) (deleteE e i)
       , toString   = toString e
       , canBranch  = f Nothing $ canBranch e
       , complete   = \i -> f (Just i) (complete e i)
       }  

--------------------------------------------------------------------------------
-- SEARCH TRANSFORMERS
--------------------------------------------------------------------------------

#ifndef NOMEMO
buildMemoKey :: MemoM m => String -> Maybe (Eval m) -> Maybe Statement -> Info -> m MemoKey
buildMemoKey fn (Just e) _ i = do 
  t <- getMemo
  return $ MemoKey { memoFn = fn, memoInfo = Just i , memoStack = Just (toString e), memoExtra = Just (memoRead t), memoStatement = Nothing, memoParams = map fst (stackField i) }
buildMemoKey fn Nothing (Just s) i = do
  return $ MemoKey { memoFn = fn, memoInfo = Nothing, memoStack = Nothing          , memoExtra = Nothing          , memoStatement = Just s , memoParams = map fst (stackField i)  }

lookupMemo :: Evalable m => String -> Maybe (Eval m) -> Maybe Statement -> Info -> m (Maybe MemoValue)
lookupMemo fn e s i = 
  do t <- getMemo
     key <- buildMemoKey fn e s i
     let r = Map.lookup key $ memoMap t
     case r of
       Nothing -> return ()
       Just k -> setMemo $ t { memoMap = Map.adjust (\x -> x { memoUsed = memoUsed x + 1 }) key (memoMap t) }
     return r

insertMemo :: Evalable m => String -> Maybe (Eval m) -> Statement -> (Int -> ([(String,Type,Value)], m Statement)) -> Info -> m MemoValue
insertMemo fn e s sm i =
  do t <- getMemo
     fl <- getFlags
     let n = memoCount t
     let (lst,ss) = sm n
     let ni = i { stackField = stackField i ++ (map (\(n,t,v) -> (rpx 0 fl t, n)) lst) }
     key <- buildMemoKey fn e (Just s) ni
     s2 <- ss
     let val = MemoValue { memoId = n
                         , memoCode = s2
                         , memoUsed = 1
                         , memoFields = stackField ni
                         }
     setMemo $ t { memoMap = Map.insert key val $ memoMap t
                 , memoCount = n+1
                 }
     return val

invokeMemo :: Evalable m => String -> Eval m -> (Eval m -> (Info -> m Statement)) -> (Info -> m Statement)
invokeMemo fn e x i = 
  do let def = x e
     r <- lookupMemo fn (Just e) Nothing i
     val <- case r of
              Nothing -> do val <- def i
                            case val of
                              Skip -> return Nothing
                              _ -> do num <- insertMemo fn (Just e) val (const ([],return val)) i
                                      return $ Just num
              Just val -> return $ Just val
     case val of
       Nothing -> return Skip
       Just x -> cacheCall (fn ++ show (memoId x)) (stackField i) []

-- cacheCall :: String -> Info -> Statement
cacheCall :: Evalable m => String -> [(String,String)] -> [Value] -> m Statement
cacheCall fn i lst = do
  fl@(PrettyFlags pf) <- getFlags
  return $ SHook (fn ++ "(" ++ intercalate "," (map snd (fixArgs pf) ++ (map snd i) ++ (map (rpx 0 fl) lst)) ++ ");")

cacheStatement_ :: Evalable m => String -> (Int -> ([(String,Type,Value)], m Statement)) -> Info -> m Statement
cacheStatement_ fn sm i = 
  do let (olst,ss) = sm 0
     fl <- getFlags
     let ni = i { stackField = stackField i ++ (map (\(n,t,v) -> (rpx 0 fl t, n)) olst) }
     s <- ss
     x <- lookupMemo fn Nothing (Just s) ni
     val <- case x of
              Nothing -> do case s of
                              Skip -> return Nothing
                              _ -> do num <- insertMemo fn Nothing s sm i
                                      return $ Just num
              Just r -> return $ Just r
     case val of
       Nothing -> return Skip
       Just x -> do let (lst,_) = sm (memoId x)
                    cacheCall (fn ++ show (memoId x)) (stackField i) (map (\(n,t,v) -> v) lst)

cacheStatement :: Evalable m => String -> Statement -> Info -> m Statement
cacheStatement fn s i = cacheStatement_ fn (const ([],return s)) i

{-
newtype MemoWrapper m a = MemoWrapper { runMemoWrapper :: m a }

instance MonadT MemoWrapper where
  lift = MemoWrapper
  treturn = MemoWrapper . return
  tbind (MemoWrapper a) f = MemoWrapper (a >>= (\x -> runMemoWrapper (f x)))

instance FMonadT MemoWrapper where
  tmap' d1 _d2 g f       = MemoWrapper . f . fmapD d1 g . runMemoWrapper
-}

class Memoable m where
  memox :: String -> Info -> (Int -> ([(String,Type,Value)],m)) -> m

instance Memoable m => Memoable ((Type,Value) -> m) where
  memox name info f = \(typ,val) -> 
    case typ of 
      THook "void" -> memox name info (\n -> let (lst,m) = f n in (lst,m (typ,Var "WTF??")))
      _ ->            memox name info (\n -> let (lst,m) = f n in (((nam n lst,typ,val):lst),m (typ,Var $ nam n lst)))
   where nam n lst = "arg_" ++ name ++ "_" ++ show n ++ "_" ++ show (length lst)

{-
instance Memoable m => Memoable (Value -> m) where
  memox name info f = \val -> memox name info (\n -> let (lst,m) = f n in (((nam n lst,Pointer (THook "void"),val):lst),m (Var $ nam n lst)))
    where nam n lst = "arg_" ++ name ++ "_" ++ show n ++ "_" ++ show (length lst)
-}

instance Evalable m => Memoable (m Statement) where
  memox name info f = cacheStatement_ ("cached_" ++ name) f info

memo :: Memoable m => String -> Info -> m -> m
memo name info m = memox name info (const ([],m))
-- memo name info m = m



memoLoop super =
  super { startTryH = invokeMemo "startTry" super startTryE 
        , bodyH = invokeMemo "body" super bodyE 
        , failH = invokeMemo "fail" super failE
        , tryH = invokeMemo "try" super tryE 
        , addH = invokeMemo "add" super addE 
        , returnH = invokeMemo "ret" super returnE
        , tryLH = invokeMemo "try_" super tryE_
        , initH = invokeMemo "init" super initE
        , pushLeftH = invokeMemo "pushL" super pushLeft
        , pushRightH = invokeMemo "pushR" super pushRight
        , deleteH = invokeMemo "delete" super deleteE
        , nextSameH = invokeMemo "nextSame" super nextSame
        , nextDiffH = invokeMemo "nextDiff" super nextDiff
        }

cachedCommit :: Evalable m => Info -> m Statement
cachedCommit i = return (comment "begin commit") @>>>@ cacheStatement "commit" (commit i) i @>>>@ return (comment "end commit")

cachedAbort :: Evalable m => Info -> m Statement
cachedAbort i = return (comment "begin abort") @>>>@ cacheStatement "abort" (abort i) i @>>>@ return (comment "end abort")

-- cachedClone :: MemoM m => Info -> Info -> m Statement
cachedClone i j = return (comment "begin clone") @>>>@ cacheStatement "clone" (cloneIt i j) i @>>>@ return (comment "end clone")
-- cachedClone i j = return $ clone i j

rReaderT x m = runMemoReaderT x m
#else

cachedCommit x = return $ (comment "begin commit" >>> commit x >>> comment "end commit")
cachedAbort x = return $ (comment "begin abort" >>> abort x >>> comment "end abort")
cachedClone i j = return $ (comment "begin clone" >>> cloneIt i j >>> comment "end clone")
memo :: String -> Info -> m -> m
memo name info m = m
memoLoop = id
rReaderT = runReaderT
#endif
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
data SeqPos = OutS | FirstS | SecondS
  deriving (Show)

seqSwitch :: ReaderM SeqPos m => m a -> m a -> m a
seqSwitch l r = 
                do flag <- ask
                   case flag  of 
                     FirstS  -> l
                     SecondS -> r

numSwitch n = 
              do flag <- ask
                 n flag

(l1,l2) @++@ (l3,l4) = (l1 ++ l3, l2 ++ l4)


ref_count = \i -> estate i @=> "ref_count"
ref_countx = \i s -> estate i @=> ("ref_count_" ++ s)
ref_count_type = THook "int"
--------------------------------------------------------------------------------

-- cloneBase i = resetClone $ info { baseTstate = estate i @=> "parent" }
cloneBase i = i { baseTstate = estate i @=> "parent" }


(@>>>@) :: Evalable m => m Statement -> m Statement -> m Statement
(@>>>@) x y = do s1 <- x
                 s2 <- y
                 return (s1 >>> s2)

f  @$ x = x >>= return . f
mf @. x = mf >>= \f -> f @$ x

--------------------------------------------------------------------------------
-- PRINTING
--------------------------------------------------------------------------------

-- printTreeStateType :: Monad m => Eval m -> String
printTreeStateType e =
  {- render $ pretty $-} Struct "TreeState" [ (ty,name) | (name,ty,_) <- treeState_ e ]

-- printEvalStateType :: Monad m => Eval m -> String
printEvalStateType e =
  {-render $ pretty $-} Struct "EvalState" [ (ty,name) | (name,ty,_) <- evalState_ e ]

-- initEvalState :: Monad m => Info -> Eval m -> Doc
initEvalState i e = mconcat $
--  {-vcat-} [SHook ((rp 0 ty) ++ " " ++ name ++ ";") | (name,ty,_) <- evalState_ e]
  [SHook "struct EvalState evalState;"]

initTreeState_ :: Monad m => Info -> Eval m -> m Statement
initTreeState_ i e = mseqs [ init i | (_,_,init) <- treeState_ e]


-- initIntArrays :: Eval m -> Doc 
initIntArrays eval =
  mconcat [ doc arr | arr <- nub $ sort $ intArraysE eval]
  where doc arr 
         | [(_,"")] <- reads arr :: [(Int,String)]
         = SHook ("vm->getSearchintVarArray(\"" ++ arr ++ "\", VAR_" ++ arr ++ ");")
         | otherwise 
         = SHook ("vm->getintVarArray(\"" ++ arr ++ "\", VAR_" ++ arr ++ ");")

-- initBoolArrays :: Eval m -> Doc 
initBoolArrays eval =
  mconcat [ doc arr | arr <- nub $ sort $ boolArraysE eval]
  where doc arr 
         | [(_,"")] <- reads arr :: [(Int,String)]
         = SHook ("vm->getSearchboolVarArray(\"" ++ arr ++ "\", VAR_" ++ arr ++ ");")
         | otherwise 
         = SHook ("vm->getboolVarArray(\"" ++ arr ++ "\", VAR_" ++ arr ++ ");")

-- declIntArrays :: Eval m -> Doc 
declIntArrays eval =
  mconcat [ doc arr | arr <- nub $ sort $ intArraysE eval]
  where doc arr 
         | [(_,"")] <- reads arr :: [(Int,String)]
         = SHook ("vector<int> VAR_" ++ arr ++ ";")
         | otherwise 
         = SHook ("vector<int> VAR_" ++ arr ++ ";")

declBoolArrays eval =
  mconcat [ doc arr | arr <- nub $ sort $ boolArraysE eval]
  where doc arr 
         | [(_,"")] <- reads arr :: [(Int,String)]
         = SHook ("vector<int> VAR_" ++ arr ++ ";")
         | otherwise 
         = SHook ("vector<int> VAR_" ++ arr ++ ";")

-- initIntVars :: Eval m -> Doc 
initIntVars eval =
  mconcat [ doc var | var <- nub $ sort $ intVarsE eval]
  where doc var = SHook ("vm->getintVarIndex(\"" ++ var ++ "\", VAR_" ++ var ++ ");")

-- declIntVars :: Eval m -> Doc 
declIntVars eval =
  mconcat [ doc var | var <- nub $ sort $ intVarsE eval]
  where doc var = SHook ("int VAR_" ++ var ++ ";")

corefn :: (Evalable m, WriterM ProgramString m) => Eval m -> m Statement
corefn eval =
  do fl <- getFlags
     sInitE <- inite (map (\(a,_,b) -> (a,b)) (evalState_ eval)) info
     sInitS <- inits eval info
     sTry   <- startTryE eval info
     sNext  <- nextSame eval info
     sBody  <- bodyE eval info
     return $ seqs [ -- SHook $ "\n  status = " ++ rpx 0 fl RootSpace ++ "->status();"
                     SHook "\n"
                   , SHook "  st->queue = new std::vector<TreeState>();"
                   , sInitE
                   , sInitS
                   , sTry
                   , Block (SHook "  while (!st->queue->empty())") $ seqs 
                     [ SHook "    /* pop first element */" 
                     , SHook "    TreeState popped_estate = st->queue->back();"
                     , SHook "    st->queue->pop_back();"
                     , sNext
                     , SHook "    st->estate = popped_estate;"
                     , sBody
                     ]
                   ]

mainfn :: (Evalable m, WriterM ProgramString m) => Eval m -> m Statement
mainfn eval =
  do core <- corefn eval
     return $ seqs [ SHook ("\n\nvoid eval(" ++ spacetype ModeFZ ++ "* root, VarMap* vm, Printer* p) {")
                   , SHook "RootState rootState;"
                   , SHook "RootState *st = &rootState;"
                   , initIntVars eval
                   , initBoolArrays eval
                   , initIntArrays eval
                   , core
                   , SHook "}"
                   ]

cppfn :: (Evalable m, WriterM ProgramString m) => Eval m -> m Statement
cppfn eval =
  do core <- corefn eval
     return $ seqs [ SHook ("\n\nvoid eval(" ++ spacetype ModeGecode ++ "* root, Printer *p) {")
                   , SHook "RootState rootState;"
                   , SHook "RootState *st = &rootState;"
                   , SHook ("    mgr.root(*root);")
                   , core
                   , SHook "}"
                   ]

mcpfn :: (Evalable m, WriterM ProgramString m) => Eval m -> m Statement
mcpfn eval =
  do core <- corefn eval
     return $ seqs [ SHook ("\n\nvoid eval(" ++ spacetype ModeMCP ++ "* root) {")
                   , SHook "RootState rootState;"
                   , SHook "RootState *st = &rootState;"
                   , core
                   , SHook "}"
                   ]

typedecls :: Evalable m => Eval m -> m Statement
typedecls eval =
  do fl <- getFlags
     return $ seqs [ SHook ("struct EvalState;")
                   , SHook (render $ vcat $ [text "struct" <+> text name <> semi | Struct name _ <- fst $ structs eval])
                   , SHook (render $ vcat $ map (prettyX fl) $ snd $ structs eval)
                   , SHook (rpx 1 fl $ printTreeStateType eval)
                   , SHook (rpx 1 fl $ printEvalStateType eval)
                   , SHook (render $ vcat $ map (prettyX fl) $ fst $ structs eval)
                   ]

declRootState :: Eval m -> Statement
declRootState eval = seqs [ SHook "typedef struct {"
                          , SHook "  TreeState estate;"
                          , SHook "  std::vector<TreeState> *queue;"
                          , initEvalState info eval
                          , SHook "} RootState;"
                          ]


generate :: (Evalable m, WriterM ProgramString m) => Eval m -> m ()
generate eval_ = 
  do fl <- getFlags
     types <- typedecls eval
     let header = seqs [ types
                       , declIntVars eval
                       , declBoolArrays eval
                       , declIntArrays eval
                       , declRootState eval
                       ]
     main <- mainfn eval
     tell $ mempty { main = Just main, header = header }
 where eval = commentEval $ eval_ { treeState_ = rootEntry ++ treeState_ eval_ }

generatemcp :: (Evalable m, WriterM ProgramString m) => Eval m -> m ()
generatemcp eval_ = 
  do fl <- getFlags
     types <- typedecls eval
     let header = seqs [ types
                       , declRootState eval
                       ]
     main <- mcpfn eval
     tell $ mempty { main = Just main, header = header }
 where eval = commentEval $ eval_ { treeState_ = rootEntry ++ treeState_ eval_ }


generatecpp :: (Evalable m, WriterM ProgramString m) => Eval m -> m ()
generatecpp eval_ = 
  do fl <- getFlags
     types <- typedecls eval
     let header = seqs [ SHook "#include \"statemgr/varaccessor.hh\""
                       , types
                       , declRootState eval
                       , SHook "StateMgr mgr;"
                       ]
     main <- cppfn eval
     tell $ mempty { main = Just main, header = header }
 where eval = commentEval $ eval_ { treeState_ = rootEntry ++ treeState_ eval_ }

rp n = render . nest n . pretty
rpx n s = render . nest n . prettyX s

--------------------------------------------------------------------------------
-- COMPOSITION COMBINATORS
--------------------------------------------------------------------------------

-- def vars = label vars lbV minV minD ($==)

type MkEval m = Evalable m => Eval m -> State Int (Eval m)

fixall :: Evalable m => MkEval m -> Eval m
fixall f = let this = fst $ runState 0 $ f this
           in this

data Search = forall t2. (FMonadT t2, MonadInfoT t2) =>
  Search { mkeval     :: forall m t1. (HookStatsM m, MonadInfoT t1, FMonadT t1, Evalable m) => MkEval ((t1 :> t2) m)
         , runsearch  :: forall m x. (Evalable m) => t2 m x -> m x
         }

#ifndef NOMEMO
memoize :: Search
memoize = 
  Search { mkeval     = return . memoLoop
         , runsearch  = runIdT
         }
#endif

{-# RULES
      "L"                          L = unsafeCoerce
  #-}
{-  # RULES
        "runL"                       runL = unsafeCoerce
  #-}
{-# RULES
        "unsafeCoerce/unsafeCoerce"  unsafeCoerce . unsafeCoerce = unsafeCoerce
  #-}
{-# RULES
        "mmap/unsafeCoerce"          mmap unsafeCoerce = unsafeCoerce
  #-}
{-# RULES
        "mapE/unsafeCoerce"          mapE unsafeCoerce = unsafeCoerce
  #-}

(<@>)
  :: Search -> Search -> Search
s1 <@> s2 = 
  case s1 of
    Search { mkeval = evals1, runsearch = runs1 } ->
      case s2 of
        Search { mkeval = evals2, runsearch = runs2 } ->
         Search {mkeval =
              \super -> do { s2' <- evals2 $ mapE (L . L . mmap runL . runL)  super
                           ; s1' <- evals1 (mapE runL s2')
                           ; return $ mapE (L . mmap L . runL) s1'
                           }
             , runsearch  = runs2 . runs1 . runL
             }


data SearchCombiner = forall t1 t2. (FMonadT t1, FMonadT t2, MonadInfoT t1, MonadInfoT t2) =>
  SearchCombiner { runner :: forall m x. Evalable m => ((t1 :> t2) m) x -> m x
                 , elems :: [SearchCombinerElem t1 t2]
                 }


data SearchCombinerElem t1 t2 =
  SearchCombinerElem { mapper :: forall t' m. (FMonadT t', MonadInfoT t', Evalable m) => Eval (t' ((t1 :> t2) m)) -> State Int (Eval (t' ((t1 :> t2) m)))
                     }


extractCombiners :: (Evalable m, FMonadT t', MonadInfoT t', FMonadT t1, MonadInfoT t1, FMonadT t2, MonadInfoT t2) => [SearchCombinerElem t1 t2] -> Eval (t' ((t1 :> t2) m)) -> State Int [(Eval (t' ((t1 :> t2) m)))]
extractCombiners [] _ = return []
extractCombiners (SearchCombinerElem { mapper=m }:b) super = 
  do prev <- extractCombiners b super
     next <- m super
     return $ (next) : prev


buildCombiner [s] =
  case s of
    Search { mkeval = evals, runsearch = runs } ->
      SearchCombiner { runner = runIdT . runs . runL
                     , elems = [SearchCombinerElem { mapper = liftM (mapE (mmap L . runL)) . evals . mapE (L . mmap runL)
                                                   }]
                     }
buildCombiner (s:ss) =
  case s of
    Search { mkeval = evals, runsearch = runs } ->
      case buildCombiner ss of
        SearchCombiner { runner = runner, elems = elems } ->
          SearchCombiner { runner = runner . runs . runL
                         , elems = SearchCombinerElem { mapper = liftM (mapE (mmap L . runL)) . evals . mapE (L . mmap runL)
                                                      } : liftSearchCombinerElems elems
                         }



liftSearchCombinerElems :: (FMonadT t1, FMonadT t0, FMonadT t2, MonadInfoT t1, MonadInfoT t0, MonadInfoT t2) => [SearchCombinerElem t1 t2] -> [SearchCombinerElem t0 (t1 :> t2)]
liftSearchCombinerElems [] = []
liftSearchCombinerElems (s:ss) = 
  case s of 
    SearchCombinerElem { mapper = m } ->
      SearchCombinerElem { mapper = liftM (mapE (mmap L . runL)) . m . mapE (L . mmap runL)
                         } : liftSearchCombinerElems ss

mmap :: (FMonadT t, MonadInfoT t, Monad m, Monad n, MonadInfo m) => (forall x. m x -> n x) -> t m a -> t n a
mmap f x = tmap' mfunctor mfunctor id f x

mfunctor :: Monad m => FunctorD m
mfunctor = FunctorD { fmapD = \f m -> m >>= return . f }

evalSStateT m s = runSStateT m s >>= \t -> case t of { Tup2 a _ -> return a }

data FunctionDef = FunctionDef { funName :: String, funArgs :: [(Type,String)], funBody :: Statement }

genfun :: PrettyFlags -> FunctionDef -> String
genfun fl f = rpx 0 fl $
    Block 
      (SHook ("void " ++ funName f ++ "(" ++ intercalate "," [ rpx 0 fl t ++ " " ++ an | (t,an) <- funArgs f ] ++ ")"))
      (funBody f)

data ProgramString = ProgramString { header :: Statement
                                   , functions :: [FunctionDef]
                                   , main :: Maybe Statement
                                   , pcomment :: [String]
                                   }

transformProgram fn p = p { header = inliner fn (header p), functions = map (\f -> f { funBody = inliner fn (funBody f) }) (functions p), main = maybe Nothing (Just . inliner fn) (main p) }

instance Monoid ProgramString where
  mempty = ProgramString { header = Skip, functions = [], main = Nothing, pcomment = [] }
  mappend p1 p2 = ProgramString { header = header p1 >>> header p2, functions = functions p1 ++ functions p2, main = maybe (main p2) Just (main p1), pcomment = pcomment p1 ++ pcomment p2 }

genprog :: PrettyFlags -> ProgramString -> String
genprog fl p = concatMap (\x -> "// " ++ x ++ "\n\n") (pcomment p) ++ rpx 0 fl (header p) ++ concatMap (\x -> "\n" ++ genfun fl x ++ "\n") (functions p) ++ maybe "" (rpx 0 fl) (main p)

monadInfo :: MInfo -> (Int,Int,Int)
monadInfo (MInfo x) = 
  let total = sum $ map snd $ Map.toList x
      identities = Map.findWithDefault 0 "Id" x + Map.findWithDefault 0 "IdT" x
      zippers = Map.findWithDefault 0 ":>" x
  in  (total - (identities+zippers),zippers,identities)

getgen :: (Evalable m, WriterM ProgramString m) => Eval m -> m ()
getgen x = do
  fl <- getFlags
  case genMode fl of
    ModeFZ -> generate x
    ModeMCP -> generatemcp x
    ModeGecode -> generatecpp x
    ModeUnk -> error "Unknown generator?"

search' :: GenMode -> Search -> ProgramString
#ifdef NOMEMO
search' fl s  = 
  case s of
    Search { mkeval = evals, runsearch = runs } -> do
       let fevals = fixall $ evals
           in case runId $ runGenModeT fl $ runHookStatsT $ evalSStateT Map.empty $ unVarInfoT $ runs $ runWriterT $ getgen $ mapE runL $ fevals
                   of (((_,eval)),n) -> let cmt = show $ monadInfo $ minfo $ canBranch $ fevals
                                            in eval { pcomment = ["Combinator stats: " ++ cmt, "Hook calls: " ++ show n]}
#else
refType t n =
  case t of
    x | last x == '*' -> n
    "int" -> n
    "bool" -> n
    _ -> '&' : n

search' fl s  = 
  case memoize <@> s of
    Search { mkeval = evals, runsearch = runs } -> do
       let fevals = fixall $ evals
           in case runId $ runGenModeT fl $ runHookStatsT $ runMemoT $ evalSStateT Map.empty $ unVarInfoT $ runs $ runWriterT $ getgen $ mapE runL $ fevals
                   of (((_,eval),t),n) -> let {- m = inlineMap t  -}
                                              p = {- transformProgram m -} (mempty { functions = map toFun (filter (not . needInline) t) } `mappend` eval)
                                              cmt = show $ monadInfo $ minfo $ canBranch $ fevals
                                          in p { pcomment = ["Combinator stats: " ++ cmt, "Hook calls: " ++ show n]}
  where toFun (key,val) = FunctionDef { funName = memoFn key ++ show (memoId val), funArgs = mm (map (\x -> (THook (fst x), refType (fst x) $ snd x)) (memoFields val)), funBody = simplify (memoCode val) }
        mm = ((fixArgs fl) ++)

fixArgs ModeMCP = [ -- (Pointer (THook "Gecode::SpaceStatus"), "status") 
                    (Pointer (THook "RootState"), "st")
                  ]
fixArgs _       = [ -- (Pointer (THook "Gecode::SpaceStatus"), "status")
                    (Pointer (THook "RootState"), "st"),
                    (Pointer (THook "Printer"),"p") 
                  ]

needInline (key,val) = False {- (memoUsed val <= 1) -}
{-needInline (key,val) = 
  let code = simplify $ memoCode val
      res = (memoUsed val <= 1) || (case code of { Seq _ _ -> False; Block _ _ -> False; Skip -> True; _ -> True })
      in trace ("needInline? " ++ show code ++ " -> " ++ show res ++ "\n") res
-}
-- needInline _ = False

inlineMap fl fns = do
  lst <- mapM (\(key,val) -> cacheCall (memoFn key ++ show (memoId val)) (memoFields val) [] >>= \c -> return (c, memoCode val)) [ x | x <- fns, needInline x ]
  return $ Map.fromList lst

#endif


search :: Search -> String
search s = genprog (PrettyFlags ModeMCP) (search' ModeMCP s)
