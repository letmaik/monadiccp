{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}

module Control.CP.SearchSpec.Generator
  ( (<@>) , (<|>) , (<&>)
  , def
  , nb
  , dbs
  , lds
  , fs
  , once
  , bbmin
  , prt
  , search
  , label
  , vlabel
  , glabel
  , foldVarSel
  , ifoldVarSel
  , until
  , failure
  , repeat
  , for, foreach
  , properLDS
  , limit
  , lbV
  , ubV
  , domsizeV      
  , lbRegretV     
  , ubRegretV     
  , degreeV       
  , wDegreeV
  , domSizeWDegreeV
  , domSizeDegreeV
  , randomV       
  , maxV
  , minV
  , minD
  , maxD    
  , meanD   
  , medianD 
  , randomD 
  , ($==)
  , ($/=)
  , ($<) 
  , ($<=)
  , ($>) 
  , ($>=)
  , (@>)
  , appStat
  , depthStat
  , nodesStat
  , discrepancyStat
  , solutionsStat
  , failsStat
  , (#>)
  ) where

import Prelude hiding (lex, until, init, repeat)
import Control.CP.SearchSpec.Language
import Text.PrettyPrint hiding (space)
import Data.List (sort, nub)
import Data.Int

{- TODO:
 - completeness
 - restart optimization
 - time limit
 - reinstate advanced variable selection
 -}

import Control.Monatron.Monatron hiding (Abort, L, state)
import Control.Monatron.Zipper hiding (i,r)
import Control.Monatron.IdT

type TreeState = Value
type EvalState = Value

data Eval m = Eval 
                 { structs    :: ([Struct],[Struct])                        -- auxiliary type declarations
                 , treeState_ :: [(String,Type, Info -> Statement)]        -- tree state fields (name, type, init)
                 , evalState  :: [(String,Type,Value)]
                 , pushLeft   :: Info -> m Statement
                 , pushRight  :: Info -> m Statement
         , bodyE      :: Info -> m Statement
                 , addE       :: Info -> m Statement
         , returnE    :: Info -> m Statement
             , failE      :: Info -> m Statement
                 , continue   :: EvalState -> m Value
                 , tryE       :: Info -> m Statement
                 , tryE_      :: Info -> m Statement
                 , intArraysE :: [String]
                 , intVarsE   :: [String]
                 }

entry name ty up = (name, ty, \i -> up (tstate i @-> name))

treeState e  =  entry "space" (Pointer SpaceType) (assign RootSpace) : treeState_ e 
space i      =  baseTstate i @-> "space"

mkCopy   i f   = (tstate i @-> f) <==   (tstate (old i) @-> f)
mkUpdate i f g = (tstate i @-> f) <== g (tstate (old i) @-> f)


pushLeftTop  e = \i -> pushLeft  e (i `onCommit` mkCopy   i "space"      )
pushRightTop e = \i -> pushRight e (i `onCommit` mkUpdate i "space" Clone)

mapE :: (forall x. m x -> n x) -> Eval m -> Eval n
mapE f e =
  Eval { structs    = structs e
       , treeState_  = treeState_ e
       , evalState  = evalState e
       , pushLeft   = f . pushLeft e
       , pushRight  = f . pushRight e
       , bodyE      = f . bodyE e
       , addE       = f . addE e
       , returnE    = f . returnE e
       , failE      = f . failE e
       , continue   = f . continue e
       , tryE       = f . tryE e
       , tryE_      = f . tryE_ e
       , intArraysE = intArraysE e
       , intVarsE   = intVarsE e
       }  

data Info = Info { baseTstate :: TreeState
                 , path       :: TreeState -> TreeState
                 , abort      :: Statement
             , commit     :: Statement
             , old        :: Info
                 , clone      :: Info -> Statement
                 , field      :: String -> Value
                 }

type Field = String

tstate i = path i (baseTstate i)
estate i = tstate i @-> "evalState"

withCommit i f   = i { commit = f (commit i) }
onAbort  i stmt  = i { abort  = stmt >>> abort i  }
onCommit i stmt  = i `withCommit` (stmt >>>)
withPath i p     = i { path   = p . path i
                     , old    = old i `withPath` p
                     }
withBase i str   = i { baseTstate = Var str }

withClone i stmt  = i { clone = \j -> clone i j >>> stmt (i { baseTstate = baseTstate j }) }
withField i (f,g) = i { field = \f' -> if f' == f then g i else field i f' }

resetPath   i     = i { path = id
                      , old  = resetPath $ old i }
resetCommit i     = i { commit = Delete $ space i }
resetClone  i     = i { clone = \j -> space j <== Clone (space i) }

mkInfo name       =
       let i = Info { baseTstate = Var name
                    , path       = id
                    , abort      = Delete $ space i
                    , commit     = Delete $ space i
                    , old        = i
                    , clone      = \j -> space j <== Clone (space i)
                    , field      = \f -> error ("unknown field `" ++ f ++ "'")
                    }
       in i

info = mkInfo "estate"

newinfo i = 
       Info { baseTstate = Var "nstate"
            , path       = id
            , abort      = Skip
        , commit     = Skip
            , old        = resetPath i
            , clone      = \j -> space j <== Clone (space i)
            , field      = \f -> error ("unknown field `" ++ f ++ "'")
            }

--------------------------------------------------------------------------------
-- LABELING
--------------------------------------------------------------------------------
data Label m = Label 
               { treeStateL   :: [(String,Type, Value -> Statement)]
                   , leftChild_L  :: [Info -> Statement]
                   , rightChild_L :: [Info -> Statement]
                   , addL         :: Info -> m Statement
                   , tryL         :: Info -> m Statement
                   , intArraysL   :: [String]
                   , intVarsL     :: [String]
                   }

v1Label var1 selVal rel e = 
            Label { treeStateL  = [("val", Int,  assign 0)
                                  ,("eq",  Bool, assign true)]
                  , leftChild_L  = 
                                  [ \i -> mkUpdate i "eq" (const true)
                                  , \i -> mkCopy i "val" ]
                  , rightChild_L =
                                  [ \i -> mkUpdate i "eq" (const false)
                                  , \i -> mkCopy i "val" ]
                  , addL        = \i -> return $
                                                 IfThenElse (eq i)
                                                   (Post (space i) (var i `rel` val i))
                                                   (Post (space i) (neg (var i `rel` val i)))
                  , tryL        = \i -> returnE e (resetPath i) >>= \ret ->
                                        tryE_ e (resetPath i)   >>= \try ->
                                        return $ (IfThenElse (Assigned (var i))
                                                          ret
                                                          (val i <== (selVal $ var i) >>> try))
                  , intArraysL  = []
                  , intVarsL    = [var1]
                  }
                  where val i = tstate i @-> "val"
                        eq  i = tstate i @-> "eq"
                        var i = VHook (rp 0 (space i) ++ "->iv[$VAR_" ++ var1 ++ "]") 

vLabel vars selVar selVal rel e = 
            Label { treeStateL  = [("pos", Int,  assign 0)
                  ,("val", Int,  assign 0)
                                  ,("eq",  Bool, assign true)]
                  , leftChild_L  = 
                                  [ \i -> mkUpdate i "eq" (const true)
                                  , \i -> mkCopy i "val"
                                  , \i -> mkCopy i "pos"]
                  , rightChild_L =
                                  [ \i -> mkUpdate i "eq" (const false)
                                  , \i -> mkCopy i "val"
                                  , \i -> mkCopy i "pos"]
                  , addL        = \i -> return $
                                                 IfThenElse (eq i)
                                                   (Post (space i) (var i `rel` val i))
                                                   (Post (space i) (neg (var i `rel` val i)))
                  , tryL        = \i -> returnE e (resetPath i) >>= \ret ->
                                        tryE_ e (resetPath i)   >>= \try ->
                                        return $ (selVar i vars
                                                          ret
                                                          (val i <== (selVal $ var i) >>> try))
                  , intArraysL  = [vars]
                  , intVarsL    = []
                  }
                  where val i = tstate i @-> "val"
                        pos i = tstate i @-> "pos"
                        eq  i = tstate i @-> "eq"
                        var i = CVar vars (space i) (pos i)

type ValSel = Value -> Value

type VarSel = Info -> String -> Statement -> Statement -> Statement

foldVarSel metric (better, zero) i vars notfound found =
  Fold vars (tstate i) (space i) zero metric better
  >>> IfThenElse (pos i @< 0) notfound found
  where pos i = tstate i @-> "pos"

ifoldVarSel metric (better, zero) i vars notfound found =
  IFold vars (tstate i) (space i) zero metric better
  >>> IfThenElse (pos i @< 0) notfound found
  where pos i = tstate i @-> "pos"

{-
lexLabel info selVal rel e = 
            Label { treeStateL  = [("pos", Int, 0)
                  ,("val", Int, 0)
                                  ,("eq",  Bool, undefined)]
                  , leftChild_L  = [("eq", const $ true)
                                  ,("val", \env -> env "val")
                                  ,("pos",\env -> env "pos")]
                  , rightChild_L = [("eq", const $ false)
                                  ,("val", \env -> env "val")
                      ,("pos",\env -> env "pos")]
                  , addL        = \state -> let space = Field state "space"
                                                var   = CVar space (Field state "pos")
                                                val   = Field state "val"
                                            in IfThenElse (Field state "eq")
                                                 (Post space (var `rel` val))
                                                 (Post space (neg (var `rel` val)))
                  , tryL        = \state -> let val   = Field state "val"
                                                space = Field state "space"
                                                var   = CVar space (Field state "pos")
                                                cmps  = [cmp | (_,(cmp,_)) <- info ]
                                                mtxs  = [ (z,f) | (f,(_,z)) <- info ]
                                             in MFold "estate" mtxs (lex cmps) 
                                                >>> IfThenElse (Field state "pos" @< 0)
                                                      (returnE e state)
                                                      (Update val (selVal var) >>> tryE_ e state)         
                  }
-}

maxV           = (Gt,IVal minBound)
minV           = (Lt,IVal maxBound)

lbV            = MinDom
ubV            = MaxDom 
domsizeV       = SizeDom
lbRegretV      = LbRegret
ubRegretV      = UbRegret
degreeV        = Degree
domSizeDegreeV = \v -> domsizeV v `Div` degreeV v
wDegreeV       = WDegree
domSizeWDegreeV= \v -> domsizeV v `Div` wDegreeV v
randomV        = const Random

minD           = MinDom
maxD           = MaxDom
meanD          = \v -> (maxD v + minD v) `Div` 2
medianD        = \v -> Median v
randomD        = \v -> (Random `Mod` (domsizeV v)) + minD v

--------------------------------------------------------------------------------
-- SEARCH TRANSFORMERS
--------------------------------------------------------------------------------

baseLoop label this = return $
        Eval { structs      = ([],[])
                 ,  treeState_   = map (\(x,y,z) -> entry x y z) $ treeStateL label  
                 ,  evalState   = []
         ,  pushLeft    = \i -> return $ commit i >>> seqs [f i | f <- leftChild_L label]  >>> Push new_tstate
         ,  pushRight   = \i -> return $ commit i >>> seqs [f i | f <- rightChild_L label] >>> Push new_tstate
         ,  bodyE       = addE this . resetPath
                 ,  addE        = \i -> tryE this (resetPath i)   >>= \try ->
                         addL label i              >>= \a   -> 
                                        failE this (resetPath i)  >>= \fail ->
                                        return $
                                                   (a 
                           >>> (Var "status" <== VHook (rp 0 (space i) ++ "->status()"))
                           >>> IfThenElse (Var "status" @== VHook "SS_FAILED")
                                                     (   fail
                             >>> Delete (space i))
                                try) 
             ,  failE      = const $ return Skip
                 ,  returnE    = \i -> return $ commit i
                 ,  continue   = \_ -> return true
                 ,  tryE       = tryL label
                 ,  tryE_      = \i -> 
                                       pushRightTop this (newinfo i)            >>= \p2 -> 
                                       pushLeftTop this  (newinfo i)            >>= \p4 ->
                       return (SHook "TreeState nstate;"
                                       >>> p2
                                       >>> p4)
                 , intArraysE  = intArraysL label
                 , intVarsE    = intVarsL label
                 }
                 where new_tstate  = Var "nstate"

--------------------------------------------------------------------------------
dummyLoop super = Eval { structs    = structs super
                       , treeState_  = treeState_ super
                       , evalState  = evalState super
               , pushLeft   = pushLeft super
               , pushRight  = pushRight super
                       , bodyE      = bodyE super
                       , addE       = addE super
                , failE      = failE super
                       , returnE    = returnE super
                       , continue   = continue super
                       , tryE       = tryE super
                       , tryE_      = tryE_ super
                       , intArraysE = intArraysE super
                       , intVarsE   = intVarsE super
                       }

failLoop super = Eval { structs    = ([],[])
                       , treeState_ = []
                       , evalState  = []
               , pushLeft   = \_ -> return Skip
               , pushRight  = \_ -> return Skip
                       , bodyE      = \i -> return $ abort i
                       , addE       = \_ -> return Skip
                , failE      = \_ -> return Skip
                       , returnE    = \_ -> return Skip
                       , continue   = \_ -> return true
                       , tryE       = \i -> return $ abort i
                       , tryE_      = \_ -> return Skip
                       , intArraysE = []
                       , intVarsE   = []
                       }

--------------------------------------------------------------------------------
data SeqPos = OutS | FirstS | SecondS

seqSwitch l r = 
                do flag <- ask
                   case flag  of 
                     FirstS  -> l
                     SecondS -> r
(l1,l2) @++@ (l3,l4) = (l1 ++ l3, l2 ++ l4)

seqLoop :: ReaderM SeqPos m => Int -> Eval m -> Eval m -> Eval m
seqLoop uid lsuper rsuper =
  Eval { structs     = structs lsuper @++@ structs rsuper @++@ mystructs 
       , treeState_   = [entry "is_fst" Bool  (assign true)
                       , ("seq_union",Union [(SType s3,"fst"),(SType s4,"snd")], 
                \i -> 
                                   let j = i `withPath` in1
                                   in  seqs [init j | (_,init) <- fs3]
                                       >>> initSubEvalState j s1 fs1
                         )]
       , evalState   = []
       , pushLeft    = push pushLeft
       , pushRight   = push pushRight
       , bodyE       = \i ->
                         let f z j = do stmt <- bodyE z (j `onAbort` dec_ref j)
                                cond <- continue z (estate j)
                                        return $ IfThenElse (cont j)
                              (IfThenElse cond
                                        stmt
                                    (   (cont j <== false)
                                                                >>> dec_ref j
                                                                >>> abort j)
                                                    )
                            (   dec_ref j
                            >>> abort j)
             in do s1 <- local (const FirstS)  $ inSeq f i
                               s2 <- local (const SecondS) $ inSeq f i
                               return $ IfThenElse (is_fst i) s1 s2
       , addE        = inSeq $ addE
       , failE       = inSeq $ \super j -> failE super j @>>>@ return (dec_ref j)
       , returnE     = \i -> let j1  = i `withPath` in1
                                 j2  = i `withPath` in2 `onCommit` dec_ref j2
                                 j2b = resetCommit j2
                             in  seqSwitch (do action <- local (const SecondS) $
                                        do stmt1 <- initTreeState_ j2b rsuper 
                                                              stmt2 <- tryE rsuper j2b
                                          return (dec_ref j1
                                                                     >>> (is_fst i <== false) 
                                                                     >>> initSubEvalState j2b s2 fs2
                                                                     >>> stmt1 >>> stmt2)
                                               returnE lsuper $ j1 `withCommit` const action
                                           )
                                           (returnE rsuper j2)
       , continue    = \_ -> return true
       , tryE        = inSeq $ tryE
       , tryE_       = inSeq $ \super j -> tryE_ super j @>>>@ return (dec_ref j)
       , intArraysE  = intArraysE lsuper ++ intArraysE rsuper
       , intVarsE    = intVarsE lsuper ++ intVarsE rsuper
       }
  where mystructs = ([s1,s2],[s3,s4])
        s1        = Struct ("LeftEvalState"  ++ show uid)  $ (Bool, "cont") : (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState lsuper]
        s2        = Struct ("RightEvalState" ++ show uid)  $ (Bool, "cont") : (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState rsuper]
        s3        = Struct ("LeftTreeState"  ++ show uid) $ (Pointer $ SType s1, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ lsuper]
        s4        = Struct ("RightTreeState" ++ show uid) $ (Pointer $ SType s2, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ rsuper]
        fs1       = [(field,init) | (field,_ty,init) <- evalState lsuper ]
        fs2       = [(field,init) | (field,_ty,init) <- evalState rsuper ]
        fs3       = [(field,init) | (field,_ty,init) <- treeState_ lsuper] 
        is_fst    = \i -> tstate i @-> "is_fst"
        cont      = \i -> estate i @=> "cont"
        ref_count = \i -> estate i @=> "ref_count"
        withSeq f = seqSwitch (f lsuper in1) (f rsuper in2)
        inSeq f   = \i -> withSeq $ \super ins -> f super (i `withPath` ins)
        dec_ref   = \j -> dec (ref_count j) >>> ifthen (ref_count j @== 0) (Delete (estate j))
        push dir  = \i -> inSeq ( \super j -> dir super (j `onCommit` (    mkCopy i "is_fst"
                                                                 >>> mkCopy j "evalState"
                                                                 >>> inc (ref_count j)
                                                                ))) i
        initSubEvalState = \j s fs ->     (estate j <== New s)  
                      >>> (ref_count j <== 1)
                          >>> (cont j <== true)
                        >>> seqs [estate j @=> f <== init | (f,init) <- fs]    

in1       = \state -> state @-> "seq_union" @-> "fst"
in2       = \state -> state @-> "seq_union" @-> "snd"
--------------------------------------------------------------------------------

cloneBase i = resetClone $ info { baseTstate = estate i @=> "parent" }

orLoop :: ReaderM SeqPos m => Int -> Eval m -> Eval m -> Eval m
orLoop uid lsuper rsuper =
  Eval { structs     = structs lsuper @++@ structs rsuper @++@ mystructs 
       , treeState_   = [entry "is_fst" Bool  (assign true)
                       , ("seq_union",Union [(SType s3,"fst"),(SType s4,"snd")], 
                \i -> 
                                   let j = i `withPath` in1
                                   in (estate j <== New s1)
                       >>> (ref_count j <== 1)
                       >>> (cont j <== true)
                                       >>> (parent j <== baseTstate j)
                                       >>> clone i (cloneBase j)
                                       >>> seqs [init (j `withClone` (\k -> inc $ ref_count k)) | (f,init) <- fs3]
                                       >>> seqs [estate j @=> f <== init | (f,init) <- fs1 ]
                         )]
       , evalState   = []
       , pushLeft    = push pushLeft
       , pushRight   = push pushRight
       , bodyE       = \i ->
                         let f y z = 
                               let j = i `withPath` y
                               in   do cond  <- continue z (estate j)
                                       deref <- dec_ref i
                       stmt  <- bodyE z (j `onAbort` deref)
                                       return $ IfThenElse (cont j)
                              (IfThenElse cond
                                        stmt
                                    (   (cont j <== false)
                                                                >>> deref
                                                                >>> abort j))
                            (deref >>> abort j)
             in IfThenElse (is_fst i) @$ local (const FirstS)  (f in1 lsuper) 
                                                  @. local (const SecondS) (f in2 rsuper)
       , addE        = inSeq $ addE
       , failE       = \i -> inSeq failE i @>>>@ dec_ref i
       , returnE     = \i -> 
                 let j1 deref = i `withPath` in1 `onCommit` deref
                                 j2 deref = i `withPath` in2 `onCommit` deref
                             in seqSwitch (dec_ref1 i >>= returnE lsuper . j1)
                                          (dec_ref2 (j2 Skip) >>= returnE rsuper . j2) 
       , continue    = \_ -> return true
       , tryE        = inSeq $ tryE 
       , tryE_       = \i -> inSeq tryE_ i @>>>@ dec_ref i
       , intArraysE  = intArraysE lsuper ++ intArraysE rsuper
       , intVarsE    = intVarsE lsuper ++ intVarsE rsuper
       }
  where mystructs = ([s1,s2],[s3,s4])
        s1        = Struct ("LeftEvalState"  ++ show uid)  $ (THook "TreeState", "parent") : (Bool, "cont") : (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState lsuper]
        fs1       = [(field,init) | (field,ty,init) <- evalState lsuper ]
        s2        = Struct ("RightEvalState" ++ show uid) $ (Bool, "cont") : (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState rsuper]
        fs2       = [(field,init) | (field,ty,init) <- evalState rsuper ]
        s3        = Struct ("LeftTreeState"  ++ show uid) $ (Pointer $ SType s1, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ lsuper]
        fs3       = [(field,init) | (field,ty,init) <- treeState_ lsuper]
        s4        = Struct ("RightTreeState" ++ show uid) $ (Pointer $ SType s2, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ rsuper]
        in1       = \state -> state @-> "seq_union" @-> "fst"
        in2       = \state -> state @-> "seq_union" @-> "snd"
        is_fst    = \i -> tstate i @-> "is_fst"
        cont      = \i -> estate i @=> "cont"
        ref_count = \i -> estate i @=> "ref_count"
        parent    = \i -> estate i @=> "parent"
        withSeq f = seqSwitch (f lsuper in1) (f rsuper in2)
        inSeq f   = \i     -> withSeq $ \super ins -> f super (i `withPath` ins)
        dec_ref    = \i -> seqSwitch (dec_ref1 i) (dec_ref2 $ i `withPath` in2)
        dec_ref1   = \i ->      let j1     = i `withPath` in1
                                    i'     = resetClone $ resetCommit $ i `withBase` ("or_tstate" ++ show uid)
                                    j2     = i' `withPath` in2
                                in (local (const SecondS) $
                                    do stmt1 <- initTreeState_ j2 rsuper 
                                       stmt2 <- tryE rsuper j2
                       return (dec (ref_count j1) 
                                               >>> ifthen (ref_count j1 @== 0) 
                                        (   SHook ("TreeState or_tstate" ++ show uid ++ ";")
                            >>> (baseTstate j2 <== parent j1)
                                                        >>> (is_fst i' <== false)
                                                        >>> Delete (estate j1)
                                                        >>> (estate j2 <== New s2)  
                                        >>> (ref_count j2 <== 1)
                                        >>> (cont j2 <== true)
                                          >>> seqs [estate j2 @=> f <== init | (f,init) <- fs2 ]    
                                                        >>> stmt1 >>> stmt2)))
        dec_ref2  = \j -> return $ dec (ref_count j) >>> ifthen (ref_count j @== 0) (Delete (estate j))
        push dir  = \i -> seqSwitch (push1 dir i) (push2 dir i)
        push1 dir = \i -> 
                           let j = i `withPath` in1 
                           in  dir lsuper (j `onCommit` (   mkCopy i "is_fst"
                                                        >>> mkCopy j "evalState"
                                                        >>> inc (ref_count j)
                                                        ))
        push2 dir = \i -> 
                           let j = i `withPath` in2 
                           in  dir rsuper (j `onCommit` (   mkCopy i "is_fst"
                                                        >>> mkCopy j "evalState"
                                                        >>> inc (ref_count j)
                                                       ))

(@>>>@) x y = do s1 <- x
                 s2 <- y
                 return (s1 >>> s2)

f  @$ x = x >>= return . f
mf @. x = mf >>= \f -> f @$ x

--------------------------------------------------------------------------------
repeatLoop :: ReaderM Bool m => Int -> Eval m -> Eval m
repeatLoop uid super =
    Eval 
       { 
         structs     = structs super @++@ mystructs 
       , treeState_  = ("dummy", Int, 
                \i -> (parent i <== baseTstate i)
                                      >>> clone i (cloneBase i)
                       ) : treeState_ super -- `withClone` (\k -> inc $ ref_count k)
       , evalState   = ("cont",Bool,true) : ("ref_count",Int,1) : ("parent",THook "TreeState",Null) : evalState super
       , pushLeft    = push pushLeft
       , pushRight   = push pushRight
       , bodyE       = \i -> do cond  <- continue super (tstate i)
                                deref <- dec_ref i
                    stmt  <- bodyE super (i `onAbort` deref)
                                return $ IfThenElse (cont i)
                              (IfThenElse cond
                                        stmt
                                    (   (cont i <== false)
                                                                >>> deref
                                                                >>> abort i))
                            (deref >>> abort i)
       , addE        = addE super
       , failE       = \i -> failE super i @>>>@ dec_ref i
       , returnE     = \i -> let j deref = i `onCommit` deref
                             in dec_ref i >>= returnE super . j
       , continue    = \_ -> return true
       , tryE        = tryE super
       , tryE_       = \i -> tryE_ super i @>>>@ dec_ref i
       , intArraysE  = intArraysE super
       , intVarsE    = intVarsE super
       }
  where mystructs = ([],[])
        fs1       = [(field,init) | (field,ty,init) <- evalState super]
        cont      = \i -> estate i @=> "cont"
        ref_count = \i -> estate i @=> "ref_count"
        parent    = \i -> estate i @=> "parent"
        dec_ref    = \i -> let i'     = resetCommit $ i `withBase` ("or_tstate" ++ show uid)
                           in do flag <- ask 
                                 if flag 
                                   then local (const False) $ do
                     stmt1 <- initTreeState_ i' super 
                                     stmt2 <- tryE super i'
                         return (dec (ref_count i) 
                                               >>> ifthen (ref_count i @== 0) 
                                       (   SHook ("TreeState or_tstate" ++ show uid ++ ";")
                              >>> (baseTstate i' <== parent i)
                           >>> clone (cloneBase i) i'
                                       >>> (ref_count i' <== 1)
                                       >>> (cont i' <== true)
                                         >>> seqs [estate i' @=> f <== init | (f,init) <- fs1 ]    
                                                   >>> stmt1 >>> stmt2))
                                   else  return $dec (ref_count i) >>> ifthen (ref_count i @== 0) (Delete (space $ cloneBase i))
        push dir  = \i -> dir super (i `onCommit` inc (ref_count i))

--------------------------------------------------------------------------------
forLoop :: ReaderM Bool m => Int32 -> Int -> (Eval m,IsComplete) -> Eval m
forLoop n uid (super,iscomplete) =
    Eval 
       { 
         structs     = structs super @++@ mystructs 
       , treeState_  = ("dummy", Int, 
                \i -> (parent i <== baseTstate i)
                                      >>> clone i (cloneBase i)
                       ) : treeState_ super
       , evalState   = ("counter",Int,0) : ("cont",Bool,true) : ("ref_count",Int,1) : ("parent",THook "TreeState",Null) : evalState super
       , pushLeft    = push pushLeft
       , pushRight   = push pushRight
       , bodyE       = \i -> do cond  <- continue super (tstate i)
                                deref <- dec_ref i
                    stmt  <- bodyE super (i `onAbort` deref)
                                return $ IfThenElse (cont i)
                              (IfThenElse cond
                                        stmt
                                    (   (cont i <== false)
                                                                >>> deref
                                                                >>> abort i))
                            (deref >>> abort i)
       , addE        = addE super
       , failE       = \i -> failE super i @>>>@ dec_ref i
       , returnE     = \i -> let j deref = i `onCommit` deref
                             in dec_ref i >>= returnE super . j
       , continue    = \_ -> return true
       , tryE        = \i -> tryE super (i `withField` ("counter", counter))
       , tryE_       = \i -> tryE_ super i @>>>@ dec_ref i
       , intArraysE  = intArraysE super
       , intVarsE    = intVarsE super
       }
  where mystructs = ([],[])
        fs1       = [(field,init) | (field,ty,init) <- evalState super]
        cont      = \i -> estate i @=> "cont"
        ref_count = \i -> estate i @=> "ref_count"
        parent    = \i -> estate i @=> "parent"
        counter   = \i -> estate i @=> "counter"
        dec_ref    = \i -> let i'     = resetCommit $ i `withBase` ("or_tstate" ++ show uid)
                           in do flag <- ask 
                                 if flag 
                                   then local (const False) $ do
                     stmt1 <- initTreeState_ i' super 
                                     stmt2 <- tryE super (i' `withField` ("counter", counter))
                         return (dec (ref_count i) 
                                               >>> ifthen (ref_count i @== 0) 
                                                     (   inc (counter i)
                                                     >>> ifthen (counter i @< IVal n &&& Not (iscomplete i))
                                           (   SHook ("TreeState or_tstate" ++ show uid ++ ";")
                                  >>> (baseTstate i' <== parent i)
                               >>> clone (cloneBase i) i'
                                           >>> (ref_count i' <== 1)
                                           >>> (cont i' <== true)
                                             >>> seqs [estate i' @=> f <== init | (f,init) <- fs1 ]    
                                                       >>> stmt1 >>> stmt2)
                             ))
                                   else  return $dec (ref_count i) >>> ifthen (ref_count i @== 0) (Delete (space $ cloneBase i))
        push dir  = \i -> dir super (i `onCommit` inc (ref_count i))

--------------------------------------------------------------------------------
untilLoop :: ReaderM SeqPos m => Stat -> Int -> (Eval m, IsComplete) -> (Eval m,IsComplete) -> Eval m
untilLoop cond uid (lsuper', liscomplete) (rsuper, riscomplete) =
  Eval { structs     = structs lsuper @++@ structs rsuper @++@ mystructs 
       , treeState_   = [entry "is_fst" Bool (assign true)
                       ,("seq_union", Union [(SType s3,"fst"),(SType s4,"snd")], 
                 \i -> 
                                   let j = i `withPath` in1
                                   in  seqs [init j | (f,init) <- fs3]
                       >>> initSubEvalState j s1 fs1)
                       ]
       , evalState   = [("until_complete",Bool,true)]
       , pushLeft    = push pushLeft
       , pushRight   = push pushRight
       , bodyE       = \i ->
                         let f y z iscomplete = 
                               let j = i `withPath` y `onAbort` dec_ref i j iscomplete
                               in   do stmt <- bodyE z j
                               cond <- continue z (estate j)
                                       return $ IfThenElse (cont j)
                              (IfThenElse cond
                                        stmt
                                    (cont j <== false >>> abort j))
                            (abort j)
             in do s1 <- local (const FirstS)  $ f in1 lsuper liscomplete
                               s2 <- local (const SecondS) $ f in2 rsuper riscomplete
                               return $ IfThenElse (is_fst i) s1 s2
       , addE        = inSeq $ addE
       , failE       = \i -> inSeq' (\super j iscomplete -> failE super j @>>>@ return (dec_ref i j iscomplete)) i
       , returnE     = \i -> inSeq' (\super j iscomplete -> returnE super (j `onCommit` dec_ref i j iscomplete)) i
       , continue    = \_ -> return true
       , tryE        = \i ->let j1 = i `withPath` in1
                                j2 = i `withPath` in2 `onAbort` dec_ref i j2 riscomplete
                            in seqSwitch (tryE lsuper j1 >>= \stmt ->
                                          (local (const SecondS) $
                                            do stmt1 <- initTreeState_ j2 rsuper 
                                               stmt2 <- tryE rsuper j2
                                               return (dec_ref i j1 liscomplete
                                                      >>> (is_fst i <== false) 
                              >>> initSubEvalState j2 s2 fs2
                                                      >>> stmt1 >>> stmt2)
                                          ) >>= \stmt2 ->
                                          return $ IfThenElse (readStat cond j1)
                                  stmt2
                                                              stmt
                                         )
                                         (tryE rsuper j2) 
       , tryE_       = \i -> inSeq' (\super j iscomplete -> tryE_ super j @>>>@ return (dec_ref i j iscomplete)) i
       , intArraysE  = intArraysE lsuper ++ intArraysE rsuper
       , intVarsE    = intVarsE lsuper ++ intVarsE rsuper
       }
  where mystructs = ([s1,s2],[s3,s4])
        s1        = Struct ("LeftEvalState"  ++ show uid)  $ (Bool, "cont") : (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState lsuper]
        fs1       = [(field,init) | (field,ty,init) <- evalState lsuper ]
        s2        = Struct ("RightEvalState" ++ show uid) $ (Bool, "cont") : (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState rsuper]
        fs2       = [(field,init) | (field,ty,init) <- evalState rsuper ]
        s3        = Struct ("LeftTreeState"  ++ show uid) $ (Pointer $ SType s1, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ lsuper]
        fs3       = [(field,init) | (field,ty,init) <- treeState_ lsuper]
        s4        = Struct ("RightTreeState" ++ show uid) $ (Pointer $ SType s2, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ rsuper]
        in1       = \state -> state @-> "seq_union" @-> "fst"
        in2       = \state -> state @-> "seq_union" @-> "snd"
        withSeq f = seqSwitch (f lsuper in1) (f rsuper in2)
        inSeq  f  = \i -> withSeq $ \super ins -> f super (i `withPath` ins)
        inSeq' f  = \i -> seqSwitch (f lsuper (i `withPath` in1) liscomplete)  
                                    (f rsuper (i `withPath` in2) riscomplete)
        dec_ref   = \i j iscomplete
                         -> dec (ref_count j) >>> 
                            ifthen (ref_count j @== 0) 
                                   (Delete (estate j) >>>
                                    (complete i <== (complete i &&& iscomplete j))
                                   )
        push dir  = \i -> seqSwitch (push1 dir i) (push2 dir i)
        push1 dir = \i -> 
                           let j = i `withPath` in1 
                           in  dir lsuper (j `onCommit` (   mkCopy i "is_fst"
                                                        >>> mkCopy j "evalState"
                                                        >>> inc (ref_count j)
                                                        ))
        push2 dir = \i -> 
                           let j = i `withPath` in2 
                           in  dir rsuper (j `onCommit` (    mkCopy i "is_fst"
                                                        >>> mkCopy j "evalState"
                                                        >>> inc (ref_count j)
                                                       ))
        lsuper = evalStat cond lsuper'
        is_fst    = \i -> tstate i @-> "is_fst"
        cont      = \i -> estate i @=> "cont"
        ref_count = \i -> estate i @=> "ref_count"
        complete  = \i -> estate i @=> "until_complete"
        initSubEvalState = \j s fs ->     (estate j <== New s)  
                      >>> (ref_count j <== 1)
                          >>> (cont j <== true)
                        >>> seqs [estate j @=> f <== init | (f,init) <- fs]    

--------------------------------------------------------------------------------
ldsLoop :: Monad m => Int32 -> MkEval m
ldsLoop limit super = return $ dummyLoop super
                     { treeState_  = entry "lds" Int (assign $ IVal limit) : treeState_ super
                     , evalState  = ("lds_complete", Bool, true) : evalState super
                     , pushLeft   = \i -> pushLeft  super (i `onCommit` mkCopy i "lds")
                     , pushRight  = \i -> pushRight super (i `onCommit` mkUpdate i "lds" (\x -> x - 1)) >>= \stmt -> 
                        return $ IfThenElse 
                               (tstate (old i) @-> "lds" @>= 0) 
                                                           stmt
                               (abort i >>> (estate i @=> "lds_complete" <== false))
                     }


--------------------------------------------------------------------------------
dbsLoop :: Monad m => Int32 -> MkEval m
dbsLoop limit super = return $ dummyLoop super
                     { treeState_  = entry "depth_limit" Int (assign $ IVal limit) : treeState_ super
                     , evalState  = ("dbs_complete", Bool, true) : evalState super
             , pushLeft   = push pushLeft
                     , pushRight  = push pushRight
                     }
  where push dir = 
      \i -> dir super (i `onCommit` mkUpdate i "depth_limit" (\x -> x - 1)) >>= \stmt ->
                return $ IfThenElse (tstate (old i) @-> "depth_limit" @>= 0)
                                    stmt
                                    ((estate i @=> "dbs_complete" <== false) >>> abort i)

--------------------------------------------------------------------------------
nbLoop :: Monad m => Int32 -> MkEval m
nbLoop limit super = return $ dummyLoop super
                     { evalState  = ("nodes", Int, IVal limit)  :
                                    ("nb_complete", Bool, true) : evalState super,
               bodyE      = \i -> bodyE super i >>= \r -> return $ dec (estate i @=> "nodes") >>> r,
                       continue   = \estate -> continue super estate >>= \r -> return $ (estate @=> "nodes" @> 0) &&& r
                     }

--------------------------------------------------------------------------------
printLoop :: Monad m => [String] -> MkEval m
printLoop arrs super = return $ dummyLoop super
                     { returnE = \i -> returnE super $ i `onCommit` Print (space i) arrs
                     }

--------------------------------------------------------------------------------
onceLoop :: Monad m => MkEval m
onceLoop super = return $ dummyLoop super
                     { evalState  = ("once",Bool,true) : evalState super
                     , returnE    = \i -> returnE super (i {commit = (estate i @=> "once" <== false) >>> commit i})
             , continue   = \estate -> continue super estate >>= \r -> return $ (estate @=> "once") &&& r
                     }

--------------------------------------------------------------------------------
nSolutionsLoop :: Monad m => Int32 -> MkEval m
nSolutionsLoop limit super = return $ dummyLoop super
                     { evalState = ("solutions", Int, IVal limit) : evalState super 
                     , returnE   = \i -> returnE super (i `onCommit` dec (estate i @=> "solutions"))
                     , continue = \estate ->  continue super estate >>= \r -> return $ (estate @=> "solutions" @> 0) &&& r
                     }

--------------------------------------------------------------------------------
bbLoop :: Monad m => String -> MkEval m 
bbLoop var super = return $ dummyLoop super
  { treeState_  = entry "tree_bound_version" Int (assign 0) : treeState_ super
  , evalState   = ("bound_version",Int,0) : ("bound",Int,IVal maxBound) : evalState super
  , returnE     = \i -> returnE super (i `onCommit`
               let get = VHook (rp 0 (space i) ++ "->getVar($VAR_" ++ var ++ ").min()")
                           in  (Update (estate i @=> "bound") get >>> inc (estate i @=> "bound_version"))) 
  , bodyE = \i -> let set = Post (space i) (VHook (rp 0 (space i) ++ "->getVar($VAR_" ++ var ++ ")") $< (estate i @=> "bound"))
                              in  do r <- bodyE super i
                                     return $ (ifthen (tstate i @-> "tree_bound_version" @< (estate i @=>"bound_version"))
                                                      (set >>> (Update (tstate i @-> "tree_bound_version") ((tstate i @-> "tree_bound_version") + 1)))
                                                           >>> r)
  , pushLeft  = push pushLeft
  , pushRight = push pushRight
  , intVarsE  = var : intVarsE super
  }
  where push dir = \i -> dir super (i `onCommit` mkCopy i "tree_bound_version")


--------------------------------------------------------------------------------
-- PRINTING
--------------------------------------------------------------------------------

printTreeStateType :: Monad m => Eval m -> String
printTreeStateType e =
  render $ pretty $ Struct "TreeState" [ (ty,name) | (name,ty,_) <- treeState e ]

initEvalState :: Monad m => Eval m -> Doc
initEvalState e =
  vcat [pretty ty <+> text name <+> (case val of { Null -> empty ; _ -> text "=" <+> pretty val}) <> text ";" | (name,ty,val) <- evalState e]

initTreeState :: Monad m => Info -> Eval m -> m Statement
initTreeState i e =
  return $ seqs [ init i | (_,_,init) <- treeState e]

initTreeState_ :: Monad m => Info -> Eval m -> m Statement
initTreeState_ i e =
  return $ seqs [ init i | (_,_,init) <- treeState_ e]

initIntArrays :: Eval m -> Doc
initIntArrays eval =
  vcat [ doc arr | arr <- nub $ sort $ intArraysE eval]
  where doc arr = text "vector<int>" <+> text "$ARR_" <> text arr <> 
          case arr of
            "branch" -> empty <+> text "=" <+> text "root->getBranchVarIds()" <> semi
            "bound" -> text "(1)" <> semi <+> text "$ARR_bound[0]=-1" <> semi

initIntVars :: Eval m -> Doc
initIntVars eval =
  vcat [ doc var | var <- nub $ sort $ intVarsE eval]
  where doc var = text "int" <+> text "$VAR_" <> text var <> 
          case var of
            "cost" -> empty <+> text "=" <+> text "-1" <> semi

-- initIntVars :: Eval m -> Doc 
-- initIntVars eval =
--   vcat [ doc var | var <- nub $ sort $ intVarsE eval]
--   where doc var = (text "int" <+> text "$VAR_" <> text var <> semi) $$
--                (text "vm->getintVarIndex(\"" <> text var <> text "\", " <> text "$VAR_" <> text var <> text ");")

generate eval = 
  do tell $ (++ "\n") $ render $ vcat $ [text "struct" <+> text name <> semi | Struct name _ <- fst $ structs eval]
     tell $ (++ "\n") $ render $ vcat $ map pretty $ snd $ structs eval
     tell $ printTreeStateType eval 
     tell $ (++ "\n") $ render $ vcat $ map pretty $ fst $ structs eval
     tell ("\n\nvoid eval(" ++ spacetype  ++ "* root) {\n")
     tell $ (++ "\n") $ render $ nest 2 $ initIntVars   eval
     tell $ (++ "\n") $ render $ nest 2 $ initIntArrays eval
     tell "\n  Gecode::SpaceStatus status = root->status();\n"
     tell "\n"
     tell "  std::list<TreeState> *queue = new std::list<TreeState>();\n"
     tell $ render (nest 2 (initEvalState eval)) ++ "\n"
     tell "  TreeState estate;\n"
     initTreeState info eval >>= tell . (++ "\n") . rp 2
     tryE eval info >>= tell . (++ "\n") . rp 2
     continue eval (estate info) >>= \c -> tell $ "  while ( !queue->empty() && (" ++ rp 0 c ++ "))  {\n"
     tell "    /* pop first element */\n" 
     tell "    estate = queue->front();\n"
     tell "    queue->pop_front();\n"
     bodyE eval info >>= tell . (++ "\n") . rp 4
     tell "  }\n"
     tell "}"

rp n = render . nest n . pretty

--------------------------------------------------------------------------------
-- TESTS
--------------------------------------------------------------------------------
testHorst = search $ prt ["q"] <@> label "q" ubV maxV minD  ($==)

--------------------------------------------------------------------------------
test0 = search $ lds 3 <@> dbs 4 <@> prt ["get"] <@> label "get" ubV maxV minD  ($==)
       

t0 = putStrLn test0
w0 f = writeFile f test0

--------------------------------------------------------------------------------
test1 = search $ lds 1000 <@> (b1 <&> (b2 <&> b3 ))
        where
            b1 = label "getP" lbV minV meanD ($<=)
            b2 = prt ["getQ"] <@> label "getQ" ubV maxV minD  ($==)
            b3 = label "getP" lbV minV meanD ($<=)

t1 = putStrLn test1
w1 f = writeFile f test1

--------------------------------------------------------------------------------
test2 = search $ nb 100 <@> (b1 <&> (b2 <&> b3))
        where
            b1 = label "get" lbV minV meanD ($<=)
            b2 = nb 5 <@> prt ["get"] <@> label "get" ubV maxV minD  ($==)
            b3 = label "get" lbV minV meanD ($<=)

t2 = putStrLn test2
w2 f = writeFile f test2

--------------------------------------------------------------------------------
test3 = search $ nb 1000 <@> (until (appStat (@> 4) depthStat) b1 b2)
        where
            b1 = label "get" lbV minV minD ($==)
            b2 = prt ["get"] <@> label "get" lbV minV maxD  ($==)


t3 = putStrLn test3
w3 f = writeFile f test3

--------------------------------------------------------------------------------
test4 = search $ dbs 10 <@> prt ["get"] <@> label "get" lbV minV minD ($==)
test5 = search $ until (appStat (@> 11) depthStat) (prt ["get"] <@> label "get" lbV minV minD ($==)) failure
--------------------------------------------------------------------------------
test6 = search $ label "get" lbV minV minD ($==) <|> label "get" lbV minV minD ($==)

----
test7 = search $ (nb 10 <@> label "getP" lbV minV minD ($==)) <&> (nb 20 <@> label "getQ" lbV minV minD ($==)) 

--------------------------------------------------------------------------------
test8 = search $ prt ["get"] <@> ((label "get" lbV minV minD ($==) <|> label "get" lbV minV minD ($==)) <|> label "get" lbV minV minD ($==))

--------------------------------------------------------------------------------
test9 = search $ prt ["get"] <@> ((b1 <&> b2) <|> b3) 
      where b1 = nb 2 <@> label "get" lbV minV minD ($==) 
            b2 = label "get" lbV minV minD ($==) 
            b3 = label "get" lbV minV minD ($==)

--------------------------------------------------------------------------------
testa = search $ prt ["get"] <@> repeat (label "get" lbV minV minD ($==))

--------------------------------------------------------------------------------
testb = search $ prt ["get"] <@> for 4 (label "get" lbV minV minD ($==))

--------------------------------------------------------------------------------
testc = search $ prt ["get"] <@> foreach 6 (\index -> until (depthStat #> index) 
                                                    (label "get" lbV minV minD ($==)) 
                                              failure
                                   )

--------------------------------------------------------------------------------
testd = search $ prt ["q"] <@> properLDS 7 (label "q" lbV minV minD ($==)) 

-- main = putStrLn test0

--------------------------------------------------------------------------------
-- COMPOSITION COMBINATORS
--------------------------------------------------------------------------------

def vars = label vars lbV minV minD ($==)

type MkEval m = Eval m -> State Int (Eval m)

fixall :: MkEval m -> Eval m
fixall f = let this = fst $ runState 0 $ f this
           in this

data Search = forall t2. FMonadT t2 =>
  Search { mkeval     :: forall m t1. (Monad m, FMonadT t1) => MkEval ((t1 :> t2) m)
         , runsearch  :: forall m x. Monad m => t2 m x -> m x
         , iscomplete :: Info -> Value
         }

type IsComplete = Info -> Value

nb :: Int32 -> Search
nb n = 
  Search { mkeval     = nbLoop n 
         , runsearch  = runIdT
         , iscomplete = const true -- DUMMY VALUE
         }

bbmin :: String -> Search
bbmin var = 
  Search { mkeval     = bbLoop var 
         , runsearch  = runIdT
         , iscomplete = const true
         }

lds :: Int32 -> Search
lds n = 
  Search { mkeval     = ldsLoop n
         , runsearch  = runIdT
         , iscomplete = \i -> estate i @=> "lds_complete"
         }

properLDS 
  :: Int32 
  -> Search
  -> Search
properLDS n search = foreach n (\limit -> until (discrepancyStat #> limit)
                                                search
                                                failure)
limit :: Int32 -> Stat -> Search -> Search
limit n stat s = until (stat #> const (IVal n)) s failure

once :: Search
once = 
  Search { mkeval     = onceLoop
         , runsearch  = runIdT
         , iscomplete = const true -- DUMMY VALUE
         } 

dbs :: Int32 -> Search
dbs n = 
  Search { mkeval     = dbsLoop n
         , runsearch  = runIdT
         , iscomplete = \i -> estate i @=> "dbs_complete"
         } 

prt :: [String] -> Search
prt str = 
  Search { mkeval     = printLoop str
         , runsearch  = runIdT
         , iscomplete = const true
         }

fs :: Search
fs =
  Search { mkeval    = nSolutionsLoop 1
         , runsearch = runIdT
         , iscomplete = const true
         }

failure :: Search
failure = 
  Search { mkeval     = return . failLoop
         , runsearch  = runIdT
         , iscomplete = const false
         }

(<@>)
  :: Search -> Search -> Search
s1 <@> s2 = 
  case s1 of
    Search { mkeval = evals1, runsearch = runs1, iscomplete = iscompletes1 } ->
      case s2 of
        Search { mkeval = evals2, runsearch = runs2, iscomplete = iscompletes2 } ->
      Search {mkeval =
              \super -> do { s2' <- evals2 $ mapE (L . L . mmap runL . runL)  super
                           ; s1' <- evals1 (mapE runL s2')
                           ; return $ mapE (L . mmap L . runL) s1'
                           }
             , runsearch  = runs2 . runs1 . runL
             , iscomplete = \i -> iscompletes1 i  &&& iscompletes2 i
             }

(<&>)
  :: Search
  -> Search
  -> Search
s1 <&> s2 = 
  case s1 of
    Search { mkeval = evals1, runsearch = runs1, iscomplete = iscompletes1 } ->
      case s2 of
        Search { mkeval = evals2, runsearch = runs2, iscomplete = iscompletes2 } ->
      Search {mkeval =
              \super -> do { s2' <- evals2 $ mapE (L . L . L . mmap (mmap runL . runL) . runL)  super
                           ; s1' <- evals1 $ mapE (L . L . mmap (mmap runL . runL) . runL) super
                   ; uid <- get
                   ; put (uid + 1)
                           ; return $ mapE (L . mmap L . runL) $ 
                           seqLoop uid (mapE (L . mmap (mmap L) . runL . runL) s1')
                                                   (mapE (L . mmap (mmap L) . runL . runL . runL) s2')
                           }
            , runsearch  = runs2 . runs1 . runL . runReaderT FirstS . runL
            , iscomplete = const true -- DUMMY VALUE
            }

(<|>)
  :: Search
  -> Search
  -> Search
s1 <|> s2 = 
  case s1 of
    Search { mkeval = evals1, runsearch = runs1, iscomplete = iscompletes1 } ->
      case s2 of
        Search { mkeval = evals2, runsearch = runs2, iscomplete = iscompletes2 } ->
      Search {mkeval =
              \super -> do { s2' <- evals2 $ mapE (L . L . L . mmap (mmap runL . runL) . runL)  super
                           ; s1' <- evals1 $ mapE (L . L . mmap (mmap runL . runL) . runL) super
                   ; uid <- get
                   ; put (uid + 1)
                           ; return $ mapE (L . mmap L . runL) $ 
                           orLoop uid (mapE (L . mmap (mmap L) . runL . runL) s1')
                                                   (mapE (L . mmap (mmap L) . runL . runL . runL) s2')
                           }
             , runsearch  = runs2 . runs1 . runL . runReaderT FirstS . runL
             , iscomplete = \i -> Cond (tstate i @-> "is_fst") (iscompletes1 (i `withPath` in1)) (iscompletes2 (i`withPath` in2))
             }

mmap :: (FMonadT t, Monad m, Monad n) => (forall x. m x -> n x) -> t m a -> t n a
mmap f x = tmap' mfunctor mfunctor id f x

mfunctor :: Monad m => FunctorD m
mfunctor = FunctorD { fmapD = \f m -> m >>= return . f }

search :: Search -> String
search s  = 
  case s of
    Search { mkeval = evals, runsearch = runs } ->
      snd $ runId $ runs $runWriterT $ generate $ mapE runL $ fixall $ evals

label :: String -> (Value -> Value) -> (Value -> Value -> Value, Value) -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
label get varMeasure varComp valSel rel = 
  Search { mkeval     = \this -> baseLoop (vLabel get (foldVarSel varMeasure varComp) valSel rel this) this 
         , runsearch  = runIdT
         , iscomplete = const true -- PROPER VALUE
         }

vlabel :: String -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
vlabel get valSel rel = 
  Search { mkeval     = \this -> baseLoop (v1Label get valSel rel this) this 
         , runsearch  = runIdT
         , iscomplete = const true -- PROPER VALUE
         }

ilabel :: String -> (Value -> Value) -> (Value -> Value -> Value, Value) -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
ilabel get varMeasure varComp valSel rel = 
  Search { mkeval     = \this -> baseLoop (vLabel get (ifoldVarSel varMeasure varComp) valSel rel this) this 
         , runsearch  = runIdT
         , iscomplete = const true -- PROPER VALUE
         }

glabel :: String -> VarSel -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
glabel get varSel valSel rel = 
  Search { mkeval     = \this -> baseLoop (vLabel get varSel valSel rel this) this 
         , runsearch  = runIdT
         , iscomplete = const true -- PROPER VALUE
         }

until 
  :: Stat
  -> Search
  -> Search
  -> Search
until cond s1 s2 = 
  case s1 of
    Search { mkeval = evals1, runsearch = runs1, iscomplete = iscompletes1 } ->
      case s2 of
        Search { mkeval = evals2, runsearch = runs2, iscomplete = iscompletes2 } ->
      Search { mkeval =
              \super -> do { s2' <- evals2 $ mapE (L . L . L . mmap (mmap runL . runL) . runL)  super
                           ; s1' <- evals1 $ mapE (L . L . mmap (mmap runL . runL) . runL) super
                      ; uid <- get
                      ; put (uid + 1)
                           ; return $ mapE (L . mmap L . runL) $ 
                       untilLoop cond uid (mapE (L . mmap (mmap L) . runL . runL) s1', iscompletes1)
                                                          (mapE (L . mmap (mmap L) . runL . runL . runL) s2', iscompletes2)
                           }
             , runsearch  = runs2 . runs1 . runL . runReaderT FirstS . runL
             , iscomplete = \i -> estate i @=> "until_complete"
             } 

repeat 
  :: Search
  -> Search
repeat s = 
  case s of
    Search { mkeval = evals, runsearch = runs, iscomplete = iscompletes } ->
      Search { mkeval =
                \super ->
               do { uid <- get
                  ; put (uid + 1)
                  ; s' <- evals $ mapE (L . L . mmap runL . runL) super
                  ; return $ mapE (L . mmap L . runL) $ repeatLoop uid $ mapE runL s' 
                  }
             , runsearch  =  runs . runReaderT True . runL
             , iscomplete = const true -- PROPER VALUE (TODO: repeat only steps when the search is complete)
             } 

for
  :: Int32
  -> Search
  -> Search
for n s  = 
  case s of
    Search { mkeval = evals, runsearch = runs, iscomplete = iscompletes } ->
      Search { mkeval =
               \super ->
               do { uid <- get
                  ; put (uid + 1)
                  ; s' <- evals $ mapE (L . L . mmap runL . runL) super
                  ; return $ mapE (L . mmap L . runL) $ forLoop n uid (mapE runL s', iscompletes)
                  }
             , runsearch   = runs . runReaderT True . runL
             , iscomplete  = iscompletes
             }

foreach
  :: Int32
  -> ((Info -> Value) -> Search)
  -> Search
foreach n mksearch  = 
        case mksearch (\i -> field i "counter")  of
          Search { mkeval = eval, runsearch = run, iscomplete = cpl } ->
           Search { mkeval = 
                    \super ->
                    do { uid <- get
                       ; put (uid + 1)
                       ; s' <- eval $ mapE (L . L . mmap runL . runL) super
                       ; return $ mapE (L . mmap L . runL) $ forLoop n uid (mapE runL s', cpl)
                       }
                  , runsearch  = run . runReaderT True . runL
                  , iscomplete = cpl
                  }

-- ========================================================================== --
-- IVALUE
-- ========================================================================== --

type IValue = Info -> Value

instance Show (Info -> Value) where
  show x  = "<IValue>"
instance Eq (Info -> Value) where
  x == y  = False

instance Num (Info -> Value) where
  x - y          = \i -> x i - y i
  fromInteger x  = \i -> IVal (fromInteger x)
  x + y          = \i -> x i + y i
  x * y          = \i -> x i * y i
  abs            = undefined
  signum         = undefined

-- ========================================================================== --
-- STATS
-- ========================================================================== --

data Stat = Stat (forall m. Monad m => Eval m -> Eval m) 
                 IValue

instance Show Stat where
  show x  = "<Stat>"
instance Eq Stat where
  x == y  = False

readStat (Stat _ r) = r
evalStat (Stat e _) = e

-- -------------------------------------------------------------------------- --

instance Num Stat where
  x - y          = undefined
  fromInteger x  = Stat dummyLoop (fromInteger x)
  x + y          = undefined
  x * y          = undefined
  abs            = undefined
  signum         = undefined

appStat :: (Value -> Value) -> Stat -> Stat
appStat f (Stat e r) = Stat e (f . r)

liftStat :: (Value -> Value -> Value) -> Stat -> IValue -> Stat
liftStat op (Stat e r) x  = Stat e (\i -> r i`op` x i)

(#>) :: Stat -> IValue -> Stat
(#>) stat x = liftStat (@>) stat x

-- -------------------------------------------------------------------------- --

depthStat :: Stat
depthStat = 
  Stat (\super -> 
               let push dir = \i -> dir super (i `onCommit` mkUpdate i "depth" (\x -> x + 1))
           in super
                     { treeState_ = entry "depth" Int (assign $ 0) : treeState_ super
             , pushLeft   = push pushLeft
                     , pushRight  = push pushRight
                     })
       (\info -> tstate info @-> "depth")

discrepancyStat :: Stat
discrepancyStat = 
  Stat 
    (\super -> 
       super
         { treeState_ = entry "discrepancy" Int (assign $ 0) : treeState_ super
         , pushLeft   = \i -> pushLeft  super (i `onCommit` mkCopy i "discrepancy")
         , pushRight  = \i -> pushRight super (i `onCommit` mkUpdate i "discrepancy" (\x -> x + 1))
         })
    (\info -> tstate info @-> "discrepancy")

nodesStat :: Stat
nodesStat = 
  eStat ("nodes", Int, 0) $
    \super -> super { bodyE = \i -> return (inc (estate i @=> "nodes")) @>>>@ bodyE super i }

solutionsStat :: Stat
solutionsStat = 
  eStat ("solutions", Int, 0) $
     \super -> super {returnE  = \i -> returnE super (i `onCommit` dec (solutions i))}
  where solutions i = estate i @=> "solutions"

failsStat :: Stat
failsStat = 
  eStat ("fails", Int, 0)
    $ \super -> super { failE = \i -> returnE super i @>>>@ return (inc (fails i)) }
  where fails i = estate i @=> "fails"

eStat :: (String, Type, Value) -> (forall m. Monad m => Eval m -> Eval m) -> Stat
eStat entry@(name,_,_) f =
  Stat (\super -> f $ super { evalState = entry : evalState super })
       (\i -> estate i @=> name)
