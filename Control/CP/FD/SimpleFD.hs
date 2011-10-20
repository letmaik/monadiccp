{-# LANGUAGE TypeFamilies #-}

module Control.CP.FD.SimpleFD (
  simple_fdSpecify,
  simple_fdProcess,
) where

import Data.List (tails)
import qualified Data.Set as Set

import Control.CP.Debug
import Control.Mixin.Mixin
import Control.CP.FD.FD
import Control.CP.Solver
import Control.CP.FD.Graph
import Data.Expr.Data
-- import Control.CP.FD.Expr.Util

itake :: [a] -> Int -> Int -> [a]
itake _ _ 0 = []
itake [] _ _ = []
itake (a:ar) 0 l = a:(itake ar 0 (l-1))
itake (a:ar) p l = itake ar (p-1) l

simple_fdSpecify :: (FDSolver s, FDColSpec s ~ [FDIntTerm s], FDIntSpec s ~ FDIntTerm s, FDBoolSpec s ~ FDBoolTerm s) => Mixin (SpecFn s)
simple_fdSpecify s t edge = case (debug ("simple_fdSpecify("++(show edge)++")") edge) of
  EGEdge { egeCons=EGAt, egeLinks = EGTypeData { colData=[c], intData=[r,p] } } -> 
    ([],[(500,r,True,do
      k <- getIntVal p
      case k of
        Just (Const kk) -> do
          Just cc <- getColSpec c
          let trm = cc !! fromInteger kk
          return $ SpecResSpec (minBound,return $ (trm, Nothing))
        _ -> return SpecResNone
    )],[])
{-  EGEdge { egeCons=EGSlice f n, egeLinks = EGTypeData { colData=[r,s] } } ->
    ([],[],[(500,r,True,do
      (Just ss) <- getColSpec s
      return $ SpecResSpec (minBound,return $ [ss !! (\(Const x) -> fromInteger x) (f i) | i <- [0..n-1]])
    )]) -}
  EGEdge { egeCons=EGCat, egeLinks = EGTypeData { colData=[r,a,b] } } ->
    ([],[],[(500,r,True,do
      Just aa <- getColSpec a
      Just bb <- getColSpec b
      return $ SpecResSpec (minBound,return (aa++bb,Nothing))
    )])
{-  EGEdge { egeCons=EGRange, egeLinks = EGTypeData { intData=[l,h], colData=[c] } } ->
    ([],[],[(550,c,False,do
      ll <- getIntVal l
      hh <- getIntVal h
      case (ll,hh) of
        (Just lll, Just hhh) -> return $ SpecResSpec (fdColSpec_size (hhh-lll+1) >>= \(t,v) -> return (t,(v,Nothing)))
        _ -> return SpecResNone
    )]) -}
  _ -> s edge

trueSpec = FDSpecInfoBool {fdspBoolSpec=const Nothing,fdspBoolVar=Nothing,fdspBoolVal=Just $ BoolConst True,fdspBoolTypes=Set.empty}

simple_fdProcess :: (FDSolver s, FDColSpec s ~ [FDIntTerm s], FDIntSpec s ~ FDIntTerm s, FDBoolSpec s ~ FDBoolTerm s) => Mixin (EGConstraintSpec -> FDSpecInfo s -> FDInstance s ())
simple_fdProcess s t cons info = case (cons,info) of
    (EGAt,(_,[r,FDSpecInfoInt {fdspIntVal = Just (Const n)}],[c])) -> do
      let cc = getDefColSpec c
          sr = getDefIntSpec r
      fdEqualInt (cc !! fromInteger n) sr
    (EGAt,(_,[r,p],[c])) -> error ("Unsupported EGAt in simple_fdProcess r="++(show r)++" p="++(show p)++" c="++(show c))
    (EGList n,(_,l,[c])) -> do
      let cc = getDefColSpec c
      sequence_ $ zipWith (\id ce -> fdEqualInt ce $ getDefIntSpec id) l cc
    (EGRange, ([],[FDSpecInfoInt {fdspIntVal = Just (Const ll)},FDSpecInfoInt {fdspIntVal=Just (Const hh)}],[c])) -> do
      let cc = getDefColSpec c
      sequence_ $ zipWith (\val var -> t (EGIntValue (Const val)) $ fdSpecInfo_spec ([],[Right (minBound,var)],[])) [ll..hh] cc
    (EGRange, ([],[FDSpecInfoInt {fdspIntVar = Just ll},FDSpecInfoInt {fdspIntVar=Just hh}],[c])) -> do
      let cc = getDefColSpec c
      l <- getIntVal ll
      h <- getIntVal hh
      case (l,h) of
        (Just (Const lll), Just (Const hhh)) -> sequence_ $ zipWith (\val var -> t (EGIntValue (Const val)) $ fdSpecInfo_spec ([],[Right (minBound,var)],[])) [lll..hhh] cc
        _ -> s cons info
    (EGRange, ([],[l,h],[c])) -> do
      error ("Unsupported EGRange in simple_fdProcess: l=("++(show l)++") h=("++(show h)++") c=("++(show c)++")")
    (EGSorted q, (_,_,[c])) -> do
      let cc = getDefColSpec c
      sequence_ $ zipWith (\a b -> t (EGLess q) $ fdSpecInfo_spec ([Left trueSpec],[Right (minBound,a), Right (minBound,b)],[])) cc (tail cc)
    (EGAllDiff _, (_,_,[c])) -> do
      let cc = getDefColSpec c
      sequence_ [ t EGDiff $ fdSpecInfo_spec ([Left trueSpec],[Right (minBound,x), Right (minBound,e)],[])  | (x:xs) <- tails cc, e <- xs ]
    (EGAll sm (nb,ni,nc) force,(r:vb,vi,c:vc)) -> do
      let dr = getDefBoolSpec r
      let dc = getDefColSpec c
      let dcs = length dc
      debug ("iter_process EGAll: dcs="++(show dcs)) $ return ()
      if force
        then do
          let mf i = do
                let v = dc!!i
                dv <- liftFD $ specInfoIntTerm v
                let fb (-1) = error "SimpleFD EGAll undefined 1"
                    fb n = vb!!n
                    fi (-1) = dv
                    fi n = vi!!n
                procSubModel sm (fb,fi,(vc!!))
          mapM_ mf [0..fromIntegral $ dcs-1]
        else do
          let mf i = do
                let v = dc!!i
                b <- liftFD $ newvar
                db <- liftFD $ specInfoBoolTerm b
                dv <- liftFD $ specInfoIntTerm v
                let fb (-1) = db
                    fb n = vb!!n
                    fi (-1) = dv
                    fi n = vi!!n
                procSubModel sm (fb,fi,(vc!!))
                return b
          bools <- mapM mf [0..fromIntegral $ dcs-1]
          treeAll t EGAnd True bools
          return ()
    (EGAny sm (nb,ni,nc) _,(r:vb,vi,c:vc)) -> do
      let dr = getDefBoolSpec r
      let dc = getDefColSpec c
      let dcs = length dc
      let mf i = do
            let v = dc!!i
            b <- liftFD $ newvar
            db <- liftFD $ specInfoBoolTerm b
            dv <- liftFD $ specInfoIntTerm v
            let fb (-1) = db
                fb n = vb!!n
                fi (-1) = dv
                fi n = vi!!n
                fc n = vc!!n
            procSubModel sm (fb,fi,fc)
            return b
      bools <- mapM mf [0..fromIntegral $ dcs-1]
      treeAll t EGOr False bools
      return ()
    (EGMap sm (nb,ni,nc),(vb,vi,cr:c:vc)) -> do
      let dc = getDefColSpec c
      let dcr = getDefColSpec cr
      let dcs = length dc
      let mf i = do
            let vin = dc!!i
            let vout = dcr!!i
            din <- liftFD $ specInfoIntTerm vin
            dout <- liftFD $ specInfoIntTerm vout
            let fi (-1) = dout
                fi (-2) = din
                fi n = vi!!n
                fb n = vb!!n
                fc n = vc!!n
            procSubModel sm (fb,fi,fc)
      mapM_ mf [0..fromIntegral $ dcs-1]
    (EGFold sm (nb,ni,nc),(vb,r:ss:vi,c:vc)) -> do
      let dc = getDefColSpec c
      let dinit = getDefIntSpec ss
      let dcs = length dc
      let dres = getDefIntSpec r
      tmp <- mapM (const $ liftFD newvar) [0..dcs-2]
      let tmpv = tmp++[dres]
      let mf i = do
            let vin1 = if (i==0) then dinit else tmpv!!(i-1)
                vout = tmpv!!i
            let vin2 = dc!!i
            din1 <- liftFD $ specInfoIntTerm vin1
            din2 <- liftFD $ specInfoIntTerm vin2
            dout <- liftFD $ specInfoIntTerm vout
            let fi (-1) = dout
                fi (-2) = din1
                fi (-3) = din2
                fi n = vi!!n
                fb n = vb!!n
                fc n = vc!!n
            procSubModel sm (fb,fi,fc)
      mapM_ mf [0..fromIntegral $ dcs-1]
    _ -> s cons info

treeAll :: (FDSolver s, FDBoolSpec s ~ FDBoolTerm s) => (EGConstraintSpec -> FDSpecInfo s -> FDInstance s ()) -> EGConstraintSpec -> Bool -> [FDBoolSpec s] -> FDInstance s (FDBoolSpec s)
treeAll p c d [] = return $ error "SimpleFD treeAll undefined"
treeAll p c d [a] = return a
treeAll p c d x = do
  let (l,r) = splitAt ((length x) `div` 2) x
  ld <- treeAll p c d l
  rd <- treeAll p c d r
  ldi <- liftFD $ specInfoBoolTerm ld
  rdi <- liftFD $ specInfoBoolTerm rd
  o <- liftFD $ newvar
  oi <- liftFD $ specInfoBoolTerm o
  p c ([oi,ldi,rdi],[],[])
  return o
