{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.CP.FD.Gecode.CodegenSolver (
  CodegenSolver(..),
  compile,
  Store(..),
  StoreNode(..),
  StoreNodeType(..),
  getVarType,
  isVarImplicit,
  VarBound(..),
  getAllBounds
) where

import Maybe (fromMaybe,catMaybes,isJust,fromJust)
import List (findIndex,find)
import Data.Map hiding (map,filter)

import Control.Monad.State.Lazy
import Control.Monad.Trans
import Control.Monad.Cont


import Control.CP.SearchTree hiding (label)
import Control.CP.Solver
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.Debug
import Control.CP.Mixin

import Control.CP.FD.Gecode.Common

--------------------------------------------------------------------------------
-- | Helper functions
--------------------------------------------------------------------------------

repl l i v = case l of
  [] -> [v]
  a:ar -> if i==0
          then v:ar
	  else repl ar (i-1) v

revrepl l i v = repl l ((length l)-i-1) v

revget l i = l !! ((length l)-i-1)

dump n l = case l of
  [] -> []
  (a:b) -> if (n==0) then b else a:(dump (n-1) b)

--------------------------------------------------------------------------------
-- | Gecode Solver instance declaration
--------------------------------------------------------------------------------
instance Solver CodegenSolver where
  type Constraint CodegenSolver = GConstraint
  type Label CodegenSolver = Store
  add   = addGecode
  run   = runGecode  
  mark  = get
  goto  = put

--------------------------------------------------------------------------------
-- | CodegenSolver terms
--------------------------------------------------------------------------------

instance Term CodegenSolver IntTerm where
  newvar = newVar False TypeInt >>= return . IntVar
  type Help CodegenSolver IntTerm = ()
  help _ _ = ()

instance Term CodegenSolver BoolTerm where
  newvar = newVar False TypeBool >>= return . BoolVar
  type Help CodegenSolver BoolTerm = ()
  help _ _ = ()

--------------------------------------------------------------------------------
-- | CodegenSolver monad definition 
--------------------------------------------------------------------------------

newtype CodegenSolver a = CodegenSolver { state :: State Store a }
  deriving (Monad, MonadState Store)

-- instance Show (CodegenSolver a) where
--   show c = show $ execState (state c) initState


type VarId = Int
type LowerBound = Maybe Integer
type UpperBound = Maybe Integer

data VarBound = VarBound { varid :: VarId, lbound :: LowerBound, ubound :: UpperBound }
  deriving (Show, Eq)

type VarBoundMap         = Map VarId VarBound
type VarBoundPropagator  = VarBoundMap -> [ VarBound ]

--------------------------------------------------------------------------------
{- |
   StoreNode represents a node in the search tree.
    * Each node adds new constraints and variables.
    * A node is a leaf node or an internal node
 -}
data StoreNode = 
  StoreNode { cons :: [ GConstraint ]
              -- ^ new constraints added in this node
            , nbounds :: [ VarBoundPropagator ]
              -- ^ new bound-generator functions in this node
            , nvars :: [ Int ]
              -- ^ id's of variables added in this node
            , dis :: StoreNodeType
              -- ^ either no children, or one left and one right child
            }

data StoreNodeType = SNLeaf | SNIntl StoreNode StoreNode
  deriving Show

instance Show StoreNode
  where show sn = "StoreNode { cons=" ++ (show $ cons sn) ++ 
                            ", nbounds=" ++ (show $ length $ nbounds sn) ++ 
                            ", nvars=" ++ (show $ nvars sn) ++ 
                            ", dus=" ++ (show $ dis sn) ++
                            "}"
--------------------------------------------------------------------------------

data VarData = VarData { vtype :: GType, vimpl :: Bool }
  deriving Show

data Store = Store { vars :: Int, vardata :: [ VarData ], ctree :: StoreNode, cpath :: [ Bool ], cexpr :: Map (ExprKey (FDTerm CodegenSolver)) Int }
  deriving Show


setVarImplicitHelper :: Store -> Int -> Bool -> Store
setVarImplicitHelper s p v = s { vardata = revrepl (vardata s) p ( (revget (vardata s) p) { vimpl = v } ) }

initNode = StoreNode { cons = [], dis = SNLeaf, nvars = [], nbounds=[] }
initState = Store { vars=0, vardata=[], ctree=initNode, cpath=[], cexpr=empty }

addStateTree node path con vars bounds = case (dis node,path) of
  (_,[]) -> node { cons = con++(cons node), nvars = vars++(nvars node), nbounds = bounds++(nbounds node) }
  (SNLeaf,s:sr) -> node { dis = if s then SNIntl initNode (addStateTree initNode sr con vars bounds) 
                                      else SNIntl (addStateTree initNode sr con vars bounds) initNode }
  (SNIntl l r,s:sr) -> node { dis = if s then SNIntl l (addStateTree r sr con vars bounds) 
                                         else SNIntl (addStateTree l sr con vars bounds) r }

addState store con vars bounds = store { ctree = addStateTree (ctree store) (cpath store) con vars bounds }

getConstraintsTree tree path = (cons tree) ++ case (dis tree,path) of
  (SNLeaf,_) -> []
  (SNIntl l _, False:s) -> getConstraintsTree l s
  (SNIntl l _, [])      -> getConstraintsTree l []
  (SNIntl _ r, True:s) -> getConstraintsTree r s


getConstraints state = getConstraintsTree (ctree state) (cpath state)

--------------------------------------------------------------------------------
-- | CodegenSolver compilation
--------------------------------------------------------------------------------

compile :: Tree CodegenSolver a -> Store
compile x = execGecode (buildState x)

execGecode :: CodegenSolver a -> Store
execGecode x = execState (state x) initState

buildState :: Tree CodegenSolver a -> CodegenSolver ()
buildState (Add c v) = do add c
                          buildState v
buildState (NewVar f) = do v <- newvar
                           buildState $ f v
buildState (Try l r)  = do v1 <- get
			   let opath = cpath v1
			   let ocexpr = cexpr v1
			   put $ v1 { cpath = opath ++ [ False ], cexpr = ocexpr }
			   buildState l
		           v2 <- get
			   put $ v2 { cpath = opath ++ [ True ], cexpr = ocexpr }
                           buildState r
			   v3 <- get
                           put $ v3 { cpath = opath, cexpr = ocexpr }
buildState (Label m) = m >>= buildState
buildState _          = return ()

--------------------------------------------------------------------------------
-- | Bounds
--------------------------------------------------------------------------------

data XInt = XInfMin | XInfPlus | XInt Integer

toXInt isUpper Nothing = if isUpper then XInfPlus else XInfMin
toXInt _ (Just i) = XInt i

bndMult (XInt a) (XInt b) _ _ = [XInt (a*b)]
bndMult XInfMin XInfMin _ _ = [XInfPlus]
bndMult XInfPlus XInfMin _ _ = [XInfMin]
bndMult XInfPlus XInfPlus _ _ = [XInfPlus]
bndMult (XInt a) XInfPlus la _
  | a < 0 = [XInfMin]
  | a > 0 =  [XInfPlus]
  | a == 0 && la = [XInfPlus]
  | a == 0 && not la = [XInfMin]
bndMult (XInt a) XInfMin la _
  | a < 0 = [XInfPlus]
  | a > 0 =  [XInfMin]
  | a == 0 && la = [XInfMin]
  | a == 0 && not la = [XInfPlus]
bndMult a b c d = bndMult b a d c

bndDiv _ _ _ _ = [XInfMin,XInfPlus]

boundFn f v1 v2 l1 l2 = f (toXInt l1 v1) (toXInt l2 v2) l1 l2

lowestBound :: [XInt] -> XInt
lowestBound = foldl1 m 
  where m XInfMin _ = XInfMin
        m _ XInfMin = XInfMin
        m (XInt a) (XInt b) = XInt $ min a b
        m (XInt a) _ = XInt a
        m _ (XInt a) = XInt a
        m XInfPlus XInfPlus = XInfPlus

highestBound :: [XInt] -> XInt
highestBound = foldl1 m 
  where m XInfPlus _ = XInfPlus
        m _ XInfPlus = XInfPlus
        m (XInt a) (XInt b) = XInt $ max a b
        m (XInt a) _ = XInt a
        m _ (XInt a) = XInt a
        m XInfMin XInfMin = XInfMin

boundRelation f (i1,i2,o) b = 
  let (i1l,i1u) = getBounds b i1
      (i2l,i2u) = getBounds b i2
      bns = foldl1 (++) $ map (\(a,b,c,d) -> boundFn f a b c d) 
        [(i1l,i2l,False,False)
        ,(i1l,i2u,False,True)
        ,(i1u,i2l,True,False)
        ,(i1u,i2u,True,True)
        ]
      xl = lowestBound bns
      xu = highestBound bns
      fromXInt XInfPlus = Nothing
      fromXInt XInfMin = Nothing
      fromXInt (XInt a) = Just a
      in case (xl,xu) of
        (XInfPlus,_) -> []
        (_,XInfMin) -> []
        (_,_) -> [VarBound { varid = o, lbound = fromXInt xl, ubound = fromXInt xu }]

catPropagators p = foldl1 (\a b -> \x -> (a x) ++ (b x)) p

linearPropagator l p c = \b -> 
  let (IntVar i,cc) = l !! p
      (low,high) = foldl 
        (\x y -> case (x,y) of
          ((Just l1,Just h1),(Just l2,Just h2)) -> (Just (l1-h2),Just (h1-l2))
          ((Nothing,Just h1),(Just l2,_)) -> (Nothing,Just (h1-l2))
          ((_,Just h1),(Just l2,Nothing)) -> (Nothing,Just (h1-l2))
          ((Just l1,Nothing),(_,Just h2)) -> (Just (l1-h2),Nothing)
          ( (Just l1,_),(Nothing,Just h2)) -> (Just (l1-h2),Nothing)
          _ -> (Nothing,Nothing)
        ) (Just c,Just c) cbounds
      cbounds = map 
        (\x -> case x of 
          (c,(Just l,Just h)) -> if c<0 then (Just (c*h),Just (c*l)) else (Just (c*l),Just (c*h))
          (c,(Nothing,Just h)) -> if c<0 then (Just (c*h),Nothing) else (Nothing,Just (c*h))
          (c,(Just l,Nothing)) -> if c<0 then (Nothing,Just (c*l)) else (Just (c*l),Nothing)
          _ -> (Nothing,Nothing)
        ) dbounds
      dbounds = dump p bounds
      bounds = map (\(IntVar v,c) -> {- debug ("var "++(show v)++" is in "++(show $ getBounds b v)) $ -} (c,getBounds b v)) l
  in (i,cc,low,high)

linearEqPropagator ll p c = \b -> case linearPropagator ll p c b of
  (_,0,_,_) -> []
  (i,cc,Just l,Just h) -> {- debug ("["++(if l>h then "AAAARGH! " else "")++(show ll)++"="++(show c)++"/"++(show cc)++"->["++(show p)++"]: var "++(show i)++" in ["++(show l)++".."++(show h)++"]]\n") $ -} if (cc<0) 
  			     then let x=[ VarBound i (Just ((-h) `div` (-cc))) (Just (l `div` cc)) ] in {- debug (show x) -} x
  			     else let x=[ VarBound i (Just ((-l) `div` (-cc))) (Just (h `div` cc)) ] in {- debug (show x) -} x
  (i,cc,Nothing,Just h) -> {- debug ("["++(show ll)++"="++(show c)++"/"++(show cc)++"->["++(show p)++"]: var "++(show i)++" in [.."++(show h)++"]]\n") $ -} if (cc<0) 
  			      then let x=[ VarBound i (Just ((-h) `div` (-cc))) Nothing ] in {- debug (show x) -} x
  			      else let x=[ VarBound i Nothing (Just (h `div` cc)) ] in {- debug (show x) -} x
  (i,cc,Just l,Nothing) -> {- debug ("["++(show ll)++"="++(show c)++"/"++(show cc)++"->["++(show p)++"]: var "++(show i)++" in ["++(show l)++"..]]\n") $ -} if (cc<0) 
  			      then let x=[ VarBound i Nothing (Just (l `div` cc)) ] in {- debug (show x) -} x
  			      else let x=[ VarBound i (Just ((-l) `div` (-cc))) Nothing ] in {- debug (show x) -} x
  (i,cc,_,_) -> {- debug ("["++(show ll)++"="++(show c)++"/"++(show cc)++"->["++(show p)++"]: var "++(show i)++" in [..]]\n") $ -} []

linearLessPropagator l p c = \b -> case (linearPropagator l p c b) of
  (_,0,_,_) -> []
  (i,cc,_,Just h) -> if (cc<0) 
  			then [ VarBound i (Just ((1-h) `div` (-cc))) Nothing ]
  			else [ VarBound i Nothing (Just ((h-1) `div` cc)) ]
  _ -> []

debugBoundsPropagator :: GConstraint -> VarBoundPropagator
debugBoundsPropagator c = let cc = boundsPropagator c in
  \b -> let ccc = cc b in {- debug ("debugBounds: "++(show c)++" -> "++(show ccc)) -} ccc

boundsPropagator :: GConstraint -> VarBoundPropagator
boundsPropagator c = case c of
  CValue (IntVar i) v -> (\_ -> [ VarBound i (Just v) (Just v) ])
  CDom (IntVar i) l u -> (\_ -> [ VarBound i (Just l) (Just u) ])
  CRel (IntVar i) OLess (IntVar j) -> \b ->
    let (jbl,jbu) = getBounds b j
        (ibl,ibu) = getBounds b i
        in catMaybes [ if isJust jbu then Just $ VarBound i Nothing (Just $ (fromJust jbu)-1) else Nothing,
                       if isJust ibl then Just $ VarBound j (Just $ (fromJust ibl)+1) Nothing else Nothing
                     ]
  CRel (IntVar i) OEqual (IntVar j) -> \b ->
    let (jbl,jbu) = getBounds b j
        (ibl,ibu) = getBounds b i
        in [ VarBound i jbl jbu, VarBound j ibl ibu ]
  CRel (IntVar i) OEqual (IntConst c) -> boundsPropagator $ CValue (IntVar i) c
  CRel (IntConst c) OEqual (IntVar i) -> boundsPropagator $ CValue (IntVar i) c
  CRel (IntVar i) OLess (IntConst c) -> (\_ -> [ VarBound i Nothing (Just (c-1)) ])
  CRel (IntConst c) OLess (IntVar i) -> (\_ -> [ VarBound i (Just (c+1)) Nothing ])
  CLinear [(IntVar i,f)] OEqual c | (c `mod` f)==0 -> boundsPropagator $ CValue (IntVar i) (c `div` f)
  CLinear l OEqual c -> catPropagators $ map (\p -> linearEqPropagator l p c) [0..((length l)-1)]
  CLinear l OLess c -> catPropagators $ map (\p -> linearLessPropagator l p c) [0..((length l)-1)]
  CMult (IntVar f1) (IntVar f2) (IntVar m) -> catPropagators
    [ boundRelation bndMult (f1,f2,m)
    , boundRelation bndDiv (m,f1,f2)
    , boundRelation bndDiv (m,f2,f1)
    ]
  CAbs (IntVar v1) (IntVar v2) -> \b ->
    let (v1l,v1h) = getBounds b v1
        (v2l,v2h) = getBounds b v2
        in [ case v2h of
               Nothing -> VarBound v1 Nothing Nothing
               Just h -> VarBound v1 (Just (-h)) (Just h)
           , case (v1l,v1h) of
               (Nothing,Nothing) -> VarBound v2 (Just 0) (Nothing)
               (Just l,Nothing) | l<0 -> VarBound v2 (Just 0) Nothing
               (Nothing,Just h) | h>0 -> VarBound v2 (Just 0) Nothing
               (Just l,Nothing) | l>=0 -> VarBound v2 (Just l) Nothing
               (Nothing,Just h) | h<=0 -> VarBound v2 (Just (-h)) Nothing
               (Just l,Just h) | l<=0 && h>=0 -> VarBound v2 (Just 0) (Just ((-l) `max` h))
               (Just l,Just h) | h<0 -> VarBound v2 (Just (-h)) (Just (-l))
               (Just l,Just h) | l>0 -> VarBound v2 (Just l) (Just h)
           ]
  _ -> (\_ -> [])

-- Combination
propagateVarBounds :: [ VarBoundPropagator ] -> VarBoundMap -> VarBoundMap
propagateVarBounds propagators vbmap  = fixP propagators vbmap
  where
   fixP :: [VarBoundPropagator] -> VarBoundMap -> VarBoundMap 
   fixP []     src  = src
   fixP (p:ps) src  = case propagate p src of
                        Nothing   -> fixP ps          src
                        Just src' -> fixP propagators src'
   propagate p src  = 
     either (const Nothing) Just $ foldl combine (Left src) (p src)
     where combine prev vb  = prev `fromMaybe` (intersectBound vb src >>= return . Right) 
                            where src = either id id prev

-- add a new bound to a bounds map - returns Nothing if map remains unchanged, Just <newmap> otherwise
intersectBound :: VarBound -> VarBoundMap -> Maybe VarBoundMap
intersectBound nw k 
   | oldValue == newValue = Nothing
   | otherwise            = Just result
    where 
     (oldValue,result) = insertLookupWithKey (\k n o -> n) (varid nw) (fromJust newValue) k
     newValue = 
       (do ov <- oldValue
           return $ adj ov
       ) `orElse` (Just nw)
     adj fnd@(VarBound {lbound = olb, ubound = oub}) = nb
       where
          nlb = newmax 1    olb $ lbound nw
          nub = newmax (-1) oub $ ubound nw
          nb = fnd { lbound = nlb, ubound = nub }
          newmax f b1 b2 = 
            (do x <- b1
                y <- b2
                return $ ((f*x) `max` (f*y)) `div` f
            ) `orElse` b1 `orElse` b2

unionBounds :: VarBoundMap -> VarBoundMap -> VarBoundMap
unionBounds = unionWith unioner
  where unioner (VarBound i1 l1 u1) (VarBound i2 l2 u2) = VarBound i1 (newmax (-1) l1 l2) (newmax 1 u1 u2)
        newmax f b1 b2 = 
          do x <- b1
             y <- b2
             return  $ ((f*x) `max` (f*y)) `div` f

getBounds :: VarBoundMap -> VarId -> (LowerBound, UpperBound)
getBounds b v = 
  let bnd = case Data.Map.lookup v b of
        Nothing -> (Nothing,Nothing)
        Just k  -> (lbound k,ubound k)
      in {- debug ("v"++(show v)++": "++(show bnd)) -} bnd

getNodeBounds :: StoreNode -> [ Bool ] -> [ VarBoundPropagator ] -> [ VarId ] -> [VarBoundMap]
getNodeBounds node path bnds vars = 
  let nvrs   = nvars   node ++ vars
      nbnds  = nbounds node ++ bnds
  in case dis node of
        SNLeaf -> [ propagateVarBounds nbnds $ fromList $ map (\x -> (x,VarBound x Nothing Nothing)) nvrs ]
        SNIntl l r -> case path of
          []   -> (getNodeBounds l [] nbnds nvrs) ++ (getNodeBounds r [] nbnds nvrs)
          x:rp -> getNodeBounds (if x then r else l) rp nbnds nvrs


getPathBounds :: Store -> [Bool] -> VarBoundMap
getPathBounds s p = foldl (flip unionBounds) empty (getNodeBounds (ctree s) p [] [])

getAllBounds s = getPathBounds s []
getCurBounds s = getPathBounds s (cpath s)

--------------------------------------------------------------------------------
-- | CodegenSolver solver implementation
--------------------------------------------------------------------------------

addGecode c = do
  s <- get
  put $ addState s [c] [] [boundsPropagator c]
  return True

newVar :: Bool -> GType -> CodegenSolver Int
newVar impl tp = do
  s <- get
  let vn = vars s
  put $ addState (s { vars = vn + 1, vardata = (VarData { vtype=tp, vimpl=impl }) : (vardata s) }) [] [vn] []
  return $ vn

runGecode :: CodegenSolver p -> p
runGecode x = evalState (state x) initState

--------------------------------------------------------------------------------
-- | CodegenSolver FDSolver instance
--------------------------------------------------------------------------------

instance GecodeSolver CodegenSolver where
  caching_decompose super this x = Label $ do
    s <- get
    let wx = ExprKey x
    case Data.Map.lookup wx (cexpr s) of
      Nothing -> return $ do
        n@(IntVar i) <- super x
        Label $ do
          s <- get
          put $ s { cexpr = insert wx i $ cexpr s }
          return $ return n
      Just i -> return $ return $ IntVar i
  setVarImplicit (IntVar i) b = do
    s <- get
    put $ setVarImplicitHelper s i b

instance FDSolver CodegenSolver where
  type FDTerm CodegenSolver = IntTerm
  specific_compile_constraint = linearCompile <@> basicCompile
  specific_decompose = caching_decompose
  specific_fresh_var super this = do
    v@(IntVar i) <- super
    Label $ do
      setVarImplicit (IntVar i) True
      return $ Return v

-- | utility

getNumVars :: Store -> Int
getNumVars s = vars s

getVarData :: Store -> Int -> VarData
getVarData s i = (vardata s) !! ((length $ vardata s)-1-i)

modVarData :: Store -> Int -> VarData -> Store
modVarData s i d = s { vardata = revrepl (vardata s) i d }

getVarType :: Store -> Int -> GType
getVarType s i = vtype $ getVarData s i

isVarImplicit :: Store -> Int -> Bool
isVarImplicit s i = vimpl $ getVarData s i
