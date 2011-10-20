module Control.CP.SearchSpec.Language  where 

import Text.PrettyPrint
import Data.Monoid
import Data.Int

spacetype = "MCPProgram"

instance Monoid Statement where
  mempty  = Skip
  mappend = (>>>)


class Pretty x where
  pretty :: x -> Doc

data Struct = Struct String [(Type,String)] deriving (Show, Eq)

instance Pretty Struct where
  pretty (Struct name fields) =
    text "struct" <+> text name <+> text "{"
    $+$ nest 2 (vcat [pretty ty <+> text f <> text ";" | (ty,f) <- fields])
    $+$ text "};" 


data Type = Pointer Type
          | SpaceType
          | Int
          | Bool
          | Union [(Type,String)]
          | SType Struct
          | THook String
          deriving (Show, Eq)

data Value = IVal Int32
           | BVal Bool
           | RootSpace
           | Minus Value Value
           | Plus Value Value
           | Div Value Value
           | Mod Value Value
           | Abs Value
           | Var String
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
           | CVar String Value Value
           | XVar String Value String
           | MinDom Value
           | MaxDom Value
           | SizeDom Value
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
           deriving (Show, Eq)

instance Num Value where
  (-)         = Minus
  fromInteger = IVal . fromInteger
  (+)    = Plus
  (*)    = undefined
  abs    = Abs
  signum = undefined

true  = BVal True
false = BVal False
(&&&) = And
(|||) = Or
(@>)  = Gt
(@>=) = Gq
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
       _             -> x'
simplValue v = v

instance Pretty Type where
  pretty (Pointer t) = pretty t <> text "*"
  pretty SpaceType      = text spacetype
  pretty Int         = text "int"
  pretty Bool        = text "bool"
  pretty (Union fields)   = 
    text "union" <+> text "{"
     $+$ nest 2 (vcat [pretty ty <+> text f <> text ";" | (ty,f) <- fields])
     $+$ text "}" 
  pretty (SType (Struct name fields))  =
    text name
  pretty (THook str) = 
    text str

instance Pretty Value where
  pretty = pretty_ . simplValue
    where
      pretty_ (Cond c t e)   = pretty c <+> text "?" <+> pretty t <+> text ":" <+> pretty e
      pretty_ Base           = text "<BASE>"
      pretty_ Null           = text "NULL"
      pretty_ (IVal i)       = int $ fromInteger $ toInteger i
      pretty_ (BVal True)    = text "true" 
      pretty_ (BVal False)   = text "false" 
      pretty_ (Abs x)        = text "abs" <> parens (pretty_ x)
      pretty_ RootSpace      = text "root"
      pretty_ (Minus v1 v2)  = pretty_ v1 <+> text "-" <+> pretty_ v2
      pretty_ (Plus v1 v2)   = pretty_ v1 <+> text "+" <+> pretty_ v2
      pretty_ (Div v1 v2)    = parens (pretty_ v1) <+> text "/" <+> parens (pretty_ v2)
      pretty_ (Mod v1 v2)    = parens (pretty_ v1) <+> text "%" <+> parens (pretty_ v2)
      pretty_ (Var x)        = text x
      pretty_ (Clone x)      = text ("static_cast<" ++ spacetype ++ "*>(") <> pretty_ x <> text "->clone(true))"
      -- pretty_ (Clone x)      = text ("static_cast<" ++ spacetype ++ "*>(") <> pretty_ x <> text "->clone(false))"
      pretty_ (Field r f)    = text r <> text "." <> text f
      pretty_ (Field' r f)   = pretty_ r <> text "." <> text f
      pretty_ (PField (Field' (Var _) "evalState") f)
                             = text f
      pretty_ (PField r f)   = pretty_ r <> text "->" <> text f
      pretty_ (Lt x y)       = parens (pretty_ x) <+> text "<" <+> parens (pretty_ y) 
      pretty_ (Gq x y)       = parens (pretty_ x) <+> text ">=" <+> parens (pretty_ y) 
      pretty_ (Gt x y)       = parens (pretty_ x) <+> text ">" <+> parens (pretty_ y) 
      pretty_ (Eq x y)       = parens (pretty_ x) <+> text "==" <+> parens (pretty_ y) 
      pretty_ BaseContinue   = text "! queue->empty()"
      pretty_ (And x y)      = parens (pretty x) <+> text "&&" <+> parens (pretty y) 
      pretty_ (Or  x y)      = parens (pretty x) <+> text "||" <+> parens (pretty y) 
      pretty_ (Not x)        = text "!" <> parens (pretty x)
      pretty_ (VHook s)      = text s
      pretty_ (Max x y)      = text "max" <> parens (pretty x <> text "," <> pretty y)
      -- pretty_ (CVar vs s i)  = pretty_ s <> text "->" <> text vs <> text "()" <> brackets (pretty i)
      pretty_ (CVar vs s i)  = pretty_ s <> text "->getVar" <> parens (text "$ARR_" <> text vs <> brackets (pretty i))
      pretty_ (XVar vs s i)  = pretty_ s <> text "->getVar" <> parens (text "$ARR_" <> text vs <> brackets (text i))
      pretty_ (MinDom v)     = pretty_ v <> text ".min()"
      pretty_ (MaxDom v)     = pretty_ v <> text ".max()"
      pretty_ (SizeDom v)    = pretty_ v <> text ".size()"
      pretty_ (Degree v)     = pretty_ v <> text ".degree()"
      pretty_ (WDegree v)    = pretty_ v <> text ".afc()" -- aka accumulated failure count
      pretty_ (UbRegret v)   = pretty_ v <> text ".regret_max()"
      pretty_ (LbRegret v)   = pretty_ v <> text ".regret_min()"
      pretty_ (Median v)     = pretty_ v <> text ".med()"
      pretty_ Random         = text "rand()"
      pretty_ (New (Struct name _)) = text "new" <+> text name
      pretty_ (Assigned var) = pretty_ var <> text ".assigned()"

data Constraint = EqC Value Value
                | NqC Value Value
                | LtC Value Value
                | LqC Value Value
                | GtC Value Value
                | GqC Value Value
                

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
  pretty (EqC x y) =
    pretty x <> text "," <> text "IRT_EQ" <> text "," <> pretty y
  pretty (NqC x y) =
    pretty x <> text "," <> text "IRT_NQ" <> text "," <> pretty y
  pretty (LtC x y) =
    pretty x <> text "," <> text "IRT_LE" <> text "," <> pretty y
  pretty (LqC x y) =
    pretty x <> text "," <> text "IRT_LQ" <> text "," <> pretty y
  pretty (GtC x y) =
    pretty x <> text "," <> text "IRT_GR" <> text "," <> pretty y
  pretty (GqC x y) =
    pretty x <> text "," <> text "IRT_GQ" <> text "," <> pretty y


data Statement = IfThenElse Value Statement Statement
               | Push Value
               | Skip
               | Update Value Value
               | Seq Statement Statement
               | Assign Value Value
	       | Abort
	       | Print Value [String]
               | SHook String
               | Post Value Constraint
               | Fold String Value Value Value (Value -> Value) (Value -> Value -> Value)
               | IFold String Value Value Value (Value -> Value) (Value -> Value -> Value)
	       | MFold String [(Value, Value->Value)] ([Value] -> [Value] -> Value)
	       | Delete Value

dec var = Update var (var - 1)
inc var = Update var (var + 1)
(>>>) = Seq
(<==) = Update
assign = flip Update
ifthen c t = IfThenElse c t Skip
seqs = foldr (>>>) Skip

instance Pretty Statement where
  pretty (Push tstate)      = 
    text "queue->push_front" <> parens (pretty tstate) <> text ";"
  pretty (IfThenElse c t e)  =
    let c' = simplValue c
    in case c' of 
         BVal True  -> pretty t
         BVal False -> pretty e
         c          -> case e of
                         Skip -> text "if" <+> parens (pretty c) <+> text "{" $+$ nest 2 (pretty t) $+$ text "}"
                         _    -> text "if" <+> parens (pretty c) <+> text "{" $+$ nest 2 (pretty t) $+$ text "} else {" $+$ nest 2 (pretty e) $+$ text "}"
  pretty Skip =
    empty
  pretty (Update var (Minus val 1))
    | var == val
    = pretty var <> text "--;"
  pretty (Update var (Plus val 1))
    | var == val
    = pretty var <> text "++;"
  pretty (Update var val)  =
    pretty var <+> text "=" <+> pretty val <> text ";"
  pretty (Seq s1 s2)  =
    pretty s1 $+$ pretty s2
  pretty (Assign x Null) = pretty x
  pretty (Assign x y)  =
    pretty x <+> text "=" <+> pretty y <> text ";"
  pretty Abort =
    text "break;"
  pretty (Print space vs) = (vcat $ map (\s -> text ("std::cout << \"[\"; for (int i=0; i<$ARR_" ++ s ++ ".size(); i++) { std::cout << ") <> pretty (XVar s space "i") <> text " << \" \"; }; std::cout << \"] \";") vs) <> text "std::cout << std::endl;"
  pretty (SHook s) =
    text s
  pretty (Post space c)  = 
    text "rel(*" <> parens (pretty space) <> text "," <> pretty c <> text ");" 
  pretty (Fold vars state space m0 metric better) = 
    let
       pos   = Field' state "pos"
       size  = VHook $ render $ text "$ARR_" <> text vars <> text ".size()" 
    in
      text "int best_pos = -1;" 
      $+$ pretty (Update pos 0)
      $+$ text "for (int metric = " <> pretty m0 <> text "; " <> pretty (pos @< size )  <> text "; "  <> pretty pos  <>  text "++) {"
      $+$ nest 2 (text "if" <+> parens (text "!" <> pretty (CVar vars space pos) <> text ".assigned()") <+> text "{"
                      $+$ nest 2 ( text "int current_metric = " <> pretty (metric (CVar vars space pos)) <> text ";"
                                   $+$ pretty (IfThenElse (Var "current_metric" `better` Var "metric")
                                                 (Update (Var "metric") (Var "current_metric") >>> (Update (Var "best_pos") pos))
                                                 Skip
                                               )
                                 )
                      $+$ text "}"
                 )
      $+$ text "}" 
      $+$ pretty (Update pos (Var "best_pos"))  
  pretty (IFold vars state space m0 metric better) = 
    let
       pos   = Field' state "pos"
       size  = VHook $ render $ text "$ARR_" <>  text vars <> text ".size()" 
    in
      text "int best_pos = -1;" 
      $+$ pretty (Update pos 0)
      $+$ text "for (int metric = " <> pretty m0 <> text "; " <> pretty (pos @< size )  <> text "; "  <> pretty pos  <>  text "++) {"
      $+$ nest 2 (text "if" <+> parens (text "!" <> pretty (CVar vars space pos) <> text ".assigned()") <+> text "{"
                      $+$ nest 2 ( text "int current_metric = " <> pretty (metric pos) <> text ";"
                                   $+$ pretty (IfThenElse (Var "current_metric" `better` Var "metric")
                                                 (Update (Var "metric") (Var "current_metric") >>> (Update (Var "best_pos") pos))
                                                 Skip
                                               )
                                 )
                      $+$ text "}"
                 )
      $+$ text "}" 
      $+$ pretty (Update pos (Var "best_pos"))  
  pretty (MFold state metrics better) = 
    let
       space         = Field "estate" "space"
       pos           = Field state "pos"
       cvar          = CVar "get" space pos
       size          = VHook $ render $ pretty space <> text "->" <> text "get" <> text "().size()" 
       acc_vars      = [Var $ "metric"         ++ show i | i <- [1..length metrics]]
       cur_vars      = [Var $ "current_metric" ++ show i | i <- [1..length metrics]]
       init_list     = hcat $ punctuate comma [pretty v <+> text "=" <+> pretty z | (v,(z,_)) <- zip acc_vars metrics]
       computations  = vcat $ [text "int" <+> pretty (Update var (f cvar))| (var,(_,f)) <- zip cur_vars metrics]
       updates       = foldl (>>>) Skip [Update v1 v2 | (v1,v2) <- zip acc_vars cur_vars]
    in
      text "int best_pos = -1;" 
      $+$ pretty (Update pos 0)
      $+$ text "for (int " <> init_list <> text "; " <> pretty (pos @< size )  <> text "; "  <> pretty pos  <>  text "++) {"
      $+$ nest 2 (text "if" <+> parens (text "!" <> pretty cvar <> text ".assigned()") <+> text "{"
                      $+$ nest 2 ( computations
                                   $+$ pretty (IfThenElse (cur_vars `better` acc_vars)
                                                 (updates >>> (Update (Var "best_pos") pos))
                                                 Skip
                                               )
                                 )
                      $+$ text "}"
                 )
      $+$ text "}" 
      $+$ pretty (Update pos (Var "best_pos"))  
  pretty (Delete value)  =
    text "delete" <+> pretty value <> text ";" 

