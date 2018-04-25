{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE CPP #-}

module Control.Search.Language  where 

import Text.PrettyPrint
import Data.Monoid hiding ((<>))
import Prelude hiding ((<>))
import qualified Data.Semigroup as DS
import Data.Int
import qualified Data.Map as Map
import Data.Map (Map)


spacetype ModeFZ = "FlatZincSpace"
spacetype ModeGecode = "State"
spacetype ModeMCP = "MCPProgram"

xsspace fl@(PrettyFlags ModeFZ) x str = prettyX fl (PField x str)
xsspace fl@(PrettyFlags ModeMCP) x str = prettyX fl (PField x str)
xsspace fl@(PrettyFlags ModeGecode) x str = text "((VarAccessorSpace*)msg.space(" <> prettyX fl x <> text "))->" <> text str

instance Monoid Statement where
  mempty  = Skip
  mappend = (>>>)

instance DS.Semigroup Statement where
  (<>) = (>>>)

data GenMode = ModeUnk | ModeGecode | ModeFZ | ModeMCP
  deriving Eq

data PrettyFlags = PrettyFlags { genMode :: GenMode }
  deriving Eq

renderVar :: PrettyFlags -> Value -> Doc
renderVar f@(PrettyFlags { genMode = ModeFZ }) x = case x of
    (AVarElem vs s i)  ->  xsspace f s "iv" <> brackets (text "VAR_" <> text vs <> brackets (pr_ i))
    (AVarSize vs s)    ->  text "VAR_" <> text vs <> text ".size()"
    (BAVarElem vs s i)  ->  xsspace f s "bv" <> brackets (text "VAR_" <> text vs <> brackets (pr_ i))
    (BAVarSize vs s)    ->  text "VAR_" <> text vs <> text ".size()"
    (IVar vs s)        ->  xsspace f s "iv" <> brackets (text "VAR_" <> text vs)
  where pr_ :: Value -> Doc
        pr_ = prettyX f
renderVar f@(PrettyFlags { genMode = ModeGecode }) x = case x of
    (AVarElem vs s i)  ->  xsspace f s "va.iv" <> parens (text "idx" <> parens (xsspace f s "va.map()" <> text ",\"" <> text vs <> text "\"") <> text "+" <> pr_ i)
    (AVarSize vs s)    ->  text "size" <> parens (xsspace f s "va.map()" <> text ",\"" <> text vs <> text "\"")
    (BAVarElem vs s i)  ->  xsspace f s "va.bv" <> parens (text "idx" <> parens (xsspace f s "va.map()" <> text ",\"" <> text vs <> text "\"") <> text "+" <> pr_ i)
    (BAVarSize vs s)    ->  text "size" <> parens (xsspace f s "va.map()" <> text ",\"" <> text vs <> text "\"")
    (IVar vs s)        ->  xsspace f s "va.iv" <> parens (text "idx" <> parens (xsspace f s "va.map()" <> text ",\"" <> text vs <> text "\""))
  where pr_ :: Value -> Doc
        pr_ = prettyX f
renderVar f@(PrettyFlags { genMode = ModeMCP }) x = case x of
    (AVarElem vs s i) -> xsspace f s vs <> brackets (pretty i)
    (AVarSize vs s) -> xsspace f s vs <> text ".size()"
    (BAVarElem vs s i) -> xsspace f s vs <> brackets (pretty i)
    (BAVarSize vs s) -> xsspace f s vs <> text ".size()"
    (IVar vs s) -> xsspace f s vs

renderVar f@(PrettyFlags { genMode = ModeUnk }) _ = error "Cannot generate variable without render mode!"


class Pretty x where
  prettyX :: PrettyFlags -> x -> Doc
  pretty :: x -> Doc
  prettyX _ = pretty
  pretty = prettyX (PrettyFlags { genMode = ModeUnk })

data Struct = Struct String [(Type,String)] deriving (Show, Eq, Ord)

instance Pretty Struct where
  prettyX x (Struct name fields) =
    text "struct" <+> text name <+> text "{"
    $+$ nest 2 (vcat [prettyX x ty <+> text f <> text ";" | (ty,f) <- fields])
    $+$ text "};" 


data Type = Pointer Type
          | SpaceType
          | Int
          | Bool
          | Union [(Type,String)]
          | SType Struct
          | THook String
          deriving (Show, Eq, Ord)

data Value = IVal Int32
           | BVal Bool
           | RootSpace
           | Minus Value Value
           | Plus Value Value
           | Mult Value Value
           | Div Value Value
           | Mod Value Value
           | Abs Value
           | Var String
           | Ref Value
           | Deref Value
           | Clone Value
           | Field String String
           | Field' Value String
           | PField Value String
           | Lt Value Value
           | Gq Value Value
           | Gt Value Value
           | Eq Value Value
           | BaseContinue
           | And Value Value
           | Or  Value Value
           | Not Value
           | VHook String
           | Max Value Value
           | AVarElem String Value Value
           | AVarSize String Value
           | BAVarElem String Value Value
           | BAVarSize String Value
           | IVar String Value
           | MinDom Value
           | MaxDom Value
           | Degree Value
           | WDegree Value
           | UbRegret Value
           | LbRegret Value
           | Median Value
           | Random 
           | Null
           | New Struct
           | Base
           | Cond Value Value Value
           | Assigned Value
           | Dummy Int
           | MaxVal
           | MinVal
           deriving (Show, Eq, Ord)

instance Num Value where
  (-)         = Minus
  fromInteger = IVal . fromInteger
  (+)    = Plus
  (*)    = Mult
  abs    = Abs
  signum = error "signum is not defined for Value"

divValue (IVal x) (IVal y) = IVal (x `div` y)
divValue x y = Div x y

true  = BVal True
false = BVal False
(&&&) = And
(|||) = Or
(@>)  = Gt
(@>=) = Gq
x @<= y = y `Gq` x
(@==) = Eq
(@->) = Field' 
(@=>) = PField 
(@<)  = Lt
lex cmps l1 l2 = foldr (\(x,y,cmp) r -> (x `cmp` y) ||| ((x @== y) &&& r)) false (zip3 l1 l2 cmps)

simplValue :: Value -> Value
simplValue (Cond c t e) =
  let c' = simplValue c
      t' = simplValue t
      e' = simplValue e
  in case (c',t',e') of
      (BVal True, _, _)  -> t'
      (BVal False, _, _) -> e'
      _  | t' == e'      -> t'
      _                  -> Cond c' t' e'
simplValue (Minus (IVal x) (IVal y)) = IVal (x - y)
simplValue (Lt x y)  = Lt (simplValue x) (simplValue y)
simplValue (Gq x y)  = Gq (simplValue x) (simplValue y)
simplValue (And x y) =
  let x' = simplValue x
      y' = simplValue y
  in case (x',y') of
       (x, (BVal True))  -> x 
       (x, (BVal False)) -> BVal False
       _                 -> And x' y'
simplValue (Not x)   =
  let x' = simplValue x
  in case x' of
       (BVal True)   -> BVal False
       (BVal False)  -> BVal True
       _             -> Not x'
simplValue (PField (Ref x) f) = Field' (simplValue x) f
simplValue v = v

instance Pretty Type where
  prettyX x (Pointer t) = prettyX x t <> text "*"
  prettyX x SpaceType      = text $ spacetype (genMode x)
  prettyX x Int         = text "int"
  prettyX x Bool        = text "bool"
  prettyX x (Union fields)   = 
    text "union" <+> text "{"
     $+$ nest 2 (vcat [prettyX x ty <+> text f <> text ";" | (ty,f) <- fields])
     $+$ text "}" 
  prettyX x (SType (Struct name fields))  =
    text name
  prettyX x (THook str) = 
    text str

instance Pretty Value where
  prettyX x = prettyX_ x . simplValue
    where
      prettyX_ :: PrettyFlags -> Value -> Doc
      prettyX_ _ (Cond c t e)   = pr_ c <+> text "?" <+> pr_ t <+> text ":" <+> pr_ e
      prettyX_ _ Base           = text "<BASE>"
      prettyX_ _ Null           = text "NULL"
      prettyX_ _ (IVal i)       = int $ fromInteger $ toInteger i
      prettyX_ _ (BVal True)    = text "true" 
      prettyX_ _ (BVal False)   = text "false" 
      prettyX_ _ (Abs x)        = text "abs" <> parens (pr_ x)
      prettyX_ fl RootSpace      = case (genMode fl) of
                                     ModeFZ -> text "root"
                                     ModeGecode -> text "mgr.root()"
                                     ModeMCP -> text "root"
      prettyX_ _ (Minus v1 v2)  = pr_ v1 <+> text "-" <+> pr_ v2
      prettyX_ _ (Plus v1 v2)   = pr_ v1 <+> text "+" <+> pr_ v2
      prettyX_ _ (Mult v1 v2)   = pr_ v1 <+> text "*" <+> pr_ v2
      prettyX_ _ (Div v1 v2)    = parens (pr_ v1) <+> text "/" <+> parens (pr_ v2)
      prettyX_ _ (Mod v1 v2)    = parens (pr_ v1) <+> text "%" <+> parens (pr_ v2)
      prettyX_ _ (Ref x)        = parens $ text "&" <> parens (pr_ x)
      prettyX_ _ (Deref x)      = parens $ text "*" <> parens (pr_ x)
      prettyX_ _ (Var x)        = text x
      prettyX_ f (Clone x)      = text ("static_cast<" ++ spacetype (genMode f) ++ "*>(") <> pr_ x <> text "->clone(true))"
      -- prettyX_ (Clone x)      = text ("static_cast<" ++ spacetype ++ "*>(") <> pretty_ x <> text "->clone(false))"
      prettyX_ _ (Field r f)    = text r <> text "." <> text f
      prettyX_ _ (Field' r f)   = pr_ r <> text "." <> text f
--      prettyX_ (PField (Field' (Var "estate") "evalState") f) = text f
--      prettyX_ (PField (Field' (Var "nstate") "evalState") f) = text f
--      prettyX_ (PField (Field' (Var _) "evalState") f) = text f
      prettyX_ _ (PField r f)   = pr_ r <> text "->" <> text f
      prettyX_ _ (Lt x y)       = parens (pr_ x) <+> text "<" <+> parens (pr_ y) 
      prettyX_ _ (Gq x y)       = parens (pr_ x) <+> text ">=" <+> parens (pr_ y) 
      prettyX_ _ (Gt x y)       = parens (pr_ x) <+> text ">" <+> parens (pr_ y) 
      prettyX_ _ (Eq x y)       = parens (pr_ x) <+> text "==" <+> parens (pr_ y) 
      prettyX_ _ BaseContinue   = text "!st->queue->empty()"
      prettyX_ _ (And x y)      = parens (pr_ x) <+> text "&&" <+> parens (pr_ y) 
      prettyX_ _ (Or  x y)      = parens (pr_ x) <+> text "||" <+> parens (pr_ y) 
      prettyX_ _ (Not x)        = text "!" <> parens (pr_ x)
      prettyX_ _ (VHook s)      = text s
      prettyX_ _ (Max x y)      = text "max" <> parens (pr_ x <> text "," <> pr_ y)
      prettyX_ e v@(AVarElem _ _ _)  = renderVar e v
      prettyX_ e v@(AVarSize _ _)  = renderVar e v
      prettyX_ e v@(BAVarElem _ _ _)  = renderVar e v
      prettyX_ e v@(BAVarSize _ _)  = renderVar e v
      prettyX_ e v@(IVar _ _)      = renderVar e v
      prettyX_ _ (MinDom v)     = pr_ v <> text ".min()"
      prettyX_ _ (MaxDom v)     = pr_ v <> text ".max()"
      prettyX_ _ (Degree v)     = pr_ v <> text ".degree()"
      prettyX_ _ (WDegree v)    = pr_ v <> text ".afc()" -- aka accumulated failure count
      prettyX_ _ (UbRegret v)   = pr_ v <> text ".regret_max()"
      prettyX_ _ (LbRegret v)   = pr_ v <> text ".regret_min()"
      prettyX_ _ (Median v)     = pr_ v <> text ".med()"
      prettyX_ _ MaxVal         = text "Gecode::Int::Limits::max"
      prettyX_ _ MinVal         = text "Gecode::Int::Limits::min"
      prettyX_ _ Random         = text "rand()"
      prettyX_ _ (New (Struct name _)) = text "new" <+> text name
      prettyX_ _ (Assigned var) = pr_ var <> text ".assigned()"
      pr :: Value -> Doc
      pr = prettyX x
      pr_ :: Value -> Doc
      pr_ = prettyX_ x

data Constraint = EqC Value Value
                | NqC Value Value
                | LtC Value Value
                | LqC Value Value
                | GtC Value Value
                | GqC Value Value
                | TrueC
                | FalseC
                deriving (Eq, Ord, Show)

($==) = EqC
($/=) = NqC
($<)  = LtC
($<=) = LqC
($>)  = GtC
($>=) = GqC

neg (EqC x y) = NqC x y
neg (NqC x y) = EqC x y
neg (LtC x y) = GqC x y
neg (LqC x y) = GtC x y
neg (GtC x y) = LqC x y
neg (GqC x y) = LtC x y

instance Pretty Constraint where
  prettyX f (EqC x y) =
    prettyX f x <> text "," <> text "IRT_EQ" <> text "," <> prettyX f y
  prettyX f (NqC x y) =
    prettyX f x <> text "," <> text "IRT_NQ" <> text "," <> prettyX f y
  prettyX f (LtC x y) =
    prettyX f x <> text "," <> text "IRT_LE" <> text "," <> prettyX f y
  prettyX f (LqC x y) =
    prettyX f x <> text "," <> text "IRT_LQ" <> text "," <> prettyX f y
  prettyX f (GtC x y) =
    prettyX f x <> text "," <> text "IRT_GR" <> text "," <> prettyX f y
  prettyX f (GqC x y) =
    prettyX f x <> text "," <> text "IRT_GQ" <> text "," <> prettyX f y
  prettyX f TrueC = error "true constraint can't be posted directly"
  prettyX f FalseC = error "false constraint can't be posted directly"


data Statement = IfThenElse Value Statement Statement
               | Push Value
               | Skip
               | Seq Statement Statement
               | Assign Value Value
               | Abort
               | Print Value [String]
               | SHook String
               | Post Value Constraint
               | Fold String Value Value Value (Value -> Value) (Value -> Value -> Value)
               | IFold String Value Value Value (Value -> Value) (Value -> Value -> Value)
               | BFold String Value Value Value (Value -> Value) (Value -> Value -> Value)
               | BIFold String Value Value Value (Value -> Value) (Value -> Value -> Value)
--             | MFold String [(Value, Value->Value)] ([Value] -> [Value] -> Value)
               | Delete Value
               | Block Statement Statement
               | DebugOutput String
               | DebugValue String Value
  deriving (Eq,Ord,Show)

inliner :: (Statement -> Maybe Statement) -> Statement -> Statement
inliner f s =
  case f s of
    Just x -> inliner f x
    Nothing -> case s of
      IfThenElse v s1 s2 -> IfThenElse v (inliner f s1) (inliner f s2)
      Seq s1 s2 -> Seq (inliner f s1) (inliner f s2)
      Block s1 s2 -> Block s1 (inliner f s2)
      _ -> s

instance Ord (Value -> Value) where
  compare a b = compare (a (Dummy 0)) (b (Dummy 0))

instance Eq (Value -> Value) where
  a == b = (a (Dummy 1)) == (b (Dummy 1))

instance Show (Value -> Value) where
  show a = show (a (Dummy 1))

instance Ord (Value -> Value -> Value) where
  compare a b = compare (a (Dummy 2) (Dummy 3)) (b (Dummy 2) (Dummy 3))

instance Eq (Value -> Value -> Value) where
  a == b = (a (Dummy 4) (Dummy 5)) == (b (Dummy 4) (Dummy 5))

instance Show (Value -> Value -> Value) where
  show a = show (a (Dummy 1) (Dummy 2))

comment str = SHook ("// " ++ str)

dec var = Assign var (var - 1)
inc var = Assign var (var + 1)
(>>>) = Seq
(<==) = Assign
assign = flip Assign
ifthen c t = IfThenElse c t Skip
seqs = foldr (>>>) Skip

simplStmt :: Statement -> Statement
simplStmt (IfThenElse c t e)
  = let c' = simplValue c
        t' = simplStmt t
        e' = simplStmt e
    in go c' t' e'
    where go (BVal True)  t e   = t
          go (BVal False) t e   = e 
          go c t e | t == e     = t
          go c Skip e           = simplStmt $ IfThenElse (Not c) e t
          go c1 (IfThenElse c2 t2 e2) e1 
            | e1 == e2          = simplStmt $ IfThenElse (c1 &&& c2) t2 e1 
          go c t e              = IfThenElse c t e
simplStmt (Assign x y) | x==y = Skip
simplStmt (Seq Skip a) = simplStmt a
simplStmt (Seq a Skip) = simplStmt a
simplStmt s = s

instance Pretty Statement where
 prettyX x = prettyX_ . simplStmt
  where
        prettyX_ (Push tstate)      = 
          text "st->queue->push_back" <> parens (pr tstate) <> text ";"
        prettyX_ (IfThenElse c t Skip)  =  text "if" <+> parens (pr c) <+> text "{" $+$ nest 2 (pr t) $+$ text "}"
        prettyX_ (IfThenElse c t e)     =  text "if" <+> parens (pr c) <+> text "{" $+$ nest 2 (pr t) $+$ text "} else {" $+$ nest 2 (pr_ e) $+$ text "}"
        prettyX_ Skip =
          empty
        prettyX_ (Assign var (Minus val 1))
          | var == val
          = pr var <> text "--;"
        prettyX_ (Assign var (Plus val 1))
          | var == val
          = pr var <> text "++;"
        prettyX_ (Block s1 s2) = pr s1 <+> text "{" $+$ nest 2 (pr s2) $+$ text "}"
        prettyX_ (Seq s1 s2)  =
          pr s1 $+$ pr s2
        prettyX_ (Assign x Null) = pr x <> text ";"
        prettyX_ (Assign x y)  = let y' = simplValue y
                               in if x == y' 
                                       then pr Skip
                                       else pr x <+> text "=" <+> pr y' <> text ";"
        prettyX_ Abort =
          text "break;"
        prettyX_ (Print space vs) = 
          (vcat $ map (\s -> text "std::cout << \"[\"; for (int i=0; i<" <> pr (AVarSize s space) <> text "; i++) { std::cout << " <> pr (AVarElem s space (Var "i")) <> text " << \" \"; }; std::cout << \"] \";") vs) <> text "std::cout << std::endl;"
        prettyX_ (DebugOutput str) = 
          text "cout << " <> text (show str) <> text " << endl;"
        prettyX_ (DebugValue str val) = 
          text "cout << " <> text (show $ str ++ ": ") <> text " << " <> pr val <> text " << endl;"
        prettyX_ (SHook s) =
          text s
        prettyX_ (Post space FalseC) = pr space <> text "->fail();"
        prettyX_ (Post space TrueC) = empty
        prettyX_ (Post space c)  = 
          text "rel(*" <> parens (pr space) <> text "," <> pr c <> text ");" 
        prettyX_ (Fold vars state space m0 metric better) = 
          let
             pos   = Field' state "pos"
             size  = AVarSize vars space
          in
            text "int best_pos = -1;" 
            $+$ pr (Assign pos 0)
            $+$ text "for (int metric = " <> pr m0 <> text "; " <> pr (pos @< size )  <> text "; "  <> pr pos  <>  text "++) {"
            $+$ nest 2 (text "if" <+> parens (text "!" <> pr (AVarElem vars space pos) <> text ".assigned()") <+> text "{"
                            $+$ nest 2 ( text "int current_metric = " <> pr (metric (AVarElem vars space pos)) <> text ";"
                                         $+$ pr (IfThenElse (Var "current_metric" `better` Var "metric")
                                                   (Assign (Var "metric") (Var "current_metric") >>> (Assign (Var "best_pos") pos))
                                                    Skip
                                                )
                                       )
                            $+$ text "}"
                       )
            $+$ text "}" 
            $+$ pr (Assign pos (Var "best_pos"))  
        prettyX_ (IFold vars state space m0 metric better) = 
          let
             pos   = Field' state "pos"
             size  = AVarSize vars state
          in
            text "int best_pos = -1;" 
            $+$ pr (Assign pos 0)
            $+$ text "for (int metric = " <> pr m0 <> text "; " <> pr (pos @< size )  <> text "; "  <> pr pos  <>  text "++) {"
            $+$ nest 2 (text "if" <+> parens (text "!" <> pr (AVarElem vars space pos) <> text ".assigned()") <+> text "{"
                            $+$ nest 2 ( text "int current_metric = " <> pr (metric pos) <> text ";"
                                         $+$ pr (IfThenElse (Var "current_metric" `better` Var "metric")
                                                      (Assign (Var "metric") (Var "current_metric") >>> (Assign (Var "best_pos") pos))
                                                      Skip
                                                )
                                       )
                            $+$ text "}"
                       )
            $+$ text "}" 
            $+$ pr (Assign pos (Var "best_pos"))  
        prettyX_ (BFold vars state space m0 metric better) = 
          let
             pos   = Field' state "pos"
             size  = BAVarSize vars space
          in
            text "int best_pos = -1;" 
            $+$ pr (Assign pos 0)
            $+$ text "for (int metric = " <> pr m0 <> text "; " <> pr (pos @< size )  <> text "; "  <> pr pos  <>  text "++) {"
            $+$ nest 2 (text "if" <+> parens (text "!" <> pr (BAVarElem vars space pos) <> text ".assigned()") <+> text "{"
                            $+$ nest 2 ( text "int current_metric = " <> pr (metric (BAVarElem vars space pos)) <> text ";"
                                         $+$ pr (IfThenElse (Var "current_metric" `better` Var "metric")
                                                   (Assign (Var "metric") (Var "current_metric") >>> (Assign (Var "best_pos") pos))
                                                    Skip
                                                )
                                       )
                            $+$ text "}"
                       )
            $+$ text "}" 
            $+$ pr (Assign pos (Var "best_pos"))  
        prettyX_ (BIFold vars state space m0 metric better) = 
          let
             pos   = Field' state "pos"
             size  = BAVarSize vars space
          in
            text "int best_pos = -1;" 
            $+$ pr (Assign pos 0)
            $+$ text "for (int metric = " <> pr m0 <> text "; " <> pr (pos @< size )  <> text "; "  <> pr pos  <>  text "++) {"
            $+$ nest 2 (text "if" <+> parens (text "!" <> pr (BAVarElem vars space pos) <> text ".assigned()") <+> text "{"
                            $+$ nest 2 ( text "int current_metric = " <> pr (metric pos) <> text ";"
                                         $+$ pr (IfThenElse (Var "current_metric" `better` Var "metric")
                                                      (Assign (Var "metric") (Var "current_metric") >>> (Assign (Var "best_pos") pos))
                                                      Skip
                                                )
                                       )
                            $+$ text "}"
                       )
            $+$ text "}" 
            $+$ pr (Assign pos (Var "best_pos"))  
{-        prettyX_ (MFold state metrics better) = 
          let
             space         = Field "estate" "space"
             pos           = Field state "pos"
             cvar          = CVar "get" space pos
             size          = VHook $ render $ pr space <> text "->" <> text "get" <> text "().size()" 
             acc_vars      = [Var $ "metric"         ++ show i | i <- [1..length metrics]]
             cur_vars      = [Var $ "current_metric" ++ show i | i <- [1..length metrics]]
             init_list     = hcat $ punctuate comma [pr v <+> text "=" <+> pretty z | (v,(z,_)) <- zip acc_vars metrics]
             computations  = vcat $ [text "int" <+> pr (Update var (f cvar))| (var,(_,f)) <- zip cur_vars metrics]
             updates       = foldl (>>>) Skip [Update v1 v2 | (v1,v2) <- zip acc_vars cur_vars]
          in
            text "int best_pos = -1;" 
            $+$ pr (Update pos 0)
            $+$ text "for (int " <> init_list <> text "; " <> pr (pos @< size )  <> text "; "  <> pr pos  <>  text "++) {"
            $+$ nest 2 (text "if" <+> parens (text "!" <> pr cvar <> text ".assigned()") <+> text "{"
                            $+$ nest 2 ( computations
                                         $+$ pr (IfThenElse (cur_vars `better` acc_vars)
                                                       (updates >>> (Update (Var "best_pos") pos))
                                                       Skip
                                                     )
                                       )
                            $+$ text "}"
                       )
            $+$ text "}" 
            $+$ pr (Update pos (Var "best_pos"))  -}
        prettyX_ (Delete value)  =
          text "delete" <+> pr value <> text ";" 
        pr :: Pretty x => x -> Doc
        pr = prettyX x
        pr_ :: Statement -> Doc
        pr_ = prettyX_


class Simplifiable a where
  simplify :: a -> a

instance Simplifiable Statement where
  simplify = simplStmt

instance Simplifiable Value where
  simplify = simplValue
