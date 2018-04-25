{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.CPP.Pretty (
  codegen
) where 

import Text.PrettyPrint.HughesPJ
import Prelude hiding ((<>))
import Language.CPP.Syntax.AST

class Pretty t where
  pretty :: t -> Doc
  prettyPrec :: Int -> t -> Doc
  pretty = prettyPrec 0
  prettyPrec _ = pretty

class ToString t where
  toString :: t -> String

instance ToString CPPAssignOp where
  toString x = case x of
    CPPAssOp    -> "="
    CPPAssOpMul -> "*="
    CPPAssOpDiv -> "/="
    CPPAssOpRmd -> "%="
    CPPAssOpAdd -> "+="
    CPPAssOpSub -> "-="
    CPPAssOpShl -> "<<="
    CPPAssOpShr -> ">>="
    CPPAssOpAnd -> "&="
    CPPAssOpOr  ->  "|="
    CPPAssOpXor -> "^="

{-
  Priorities in C (http://www.difranco.net/cop2220/op-prec.htm)
 
  2:  comma
  4:  assignments
  6:  conditional
  8:  logical or
  10:  logical and
  12:  bitwise or
  14:  bitwise xor
  16:  bitwise and
  18:  equality/inequality test
  20: relational tests
  22: bitshift
  24: addition/subtraction
  26: multiplication/division/modulus
  28: preincrement/predecrement/negation/complement/cast/dereference/address/sizeof
  30: brackets/index/member/postincrement/postdecrement/
-}


instance Pretty CPPConst where
  pretty (CPPConstInt x) = text $ show x
  pretty (CPPConstChar x) = text $ "'" ++ x ++ "'"   -- TODO: character escaping
  pretty (CPPConstString x) = text $ "\"" ++ x ++ "\""
  pretty (CPPConstFloat x) = text x

prio :: Int -> Int -> Doc -> Doc
prio myL outerL doc = if myL<outerL then parens doc else doc

instance Pretty CPPExpr where
  prettyPrec l (CPPConst x) = prettyPrec l x
  prettyPrec l (CPPAssign o1 op o2) = prio 4 l $ (prettyPrec 5 o1) <+> (text $ toString op) <+> (prettyPrec 4 o2)
  prettyPrec l (CPPVar v) = text v
  prettyPrec l (CPPComma lst) = lparen <> (foldl (<>) empty $ punctuate comma $ map (prettyPrec 2) lst) <> rparen
  prettyPrec l (CPPBinary o1 CPPOpMul  o2) = prio 26 l $ (prettyPrec 26 o1) <> text "*"  <> (prettyPrec 27 o2)
  prettyPrec l (CPPBinary o1 CPPOpDiv  o2) = prio 26 l $ (prettyPrec 26 o1) <> text "/"  <> (prettyPrec 27 o2)
  prettyPrec l (CPPBinary o1 CPPOpRmd  o2) = prio 26 l $ (prettyPrec 26 o1) <> text "%"  <> (prettyPrec 27 o2)
  prettyPrec l (CPPBinary o1 CPPOpAdd  o2) = prio 24 l $ (prettyPrec 24 o1) <> text "+"  <> (prettyPrec 24 o2)
  prettyPrec l (CPPBinary o1 CPPOpSub  o2) = prio 24 l $ (prettyPrec 24 o1) <> text "-"  <> (prettyPrec 25 o2)
  prettyPrec l (CPPBinary o1 CPPOpShl  o2) = prio 22 l $ (prettyPrec 22 o1) <> text "<<" <> (prettyPrec 23 o2)
  prettyPrec l (CPPBinary o1 CPPOpShr  o2) = prio 22 l $ (prettyPrec 22 o1) <> text ">>" <> (prettyPrec 23 o2)
  prettyPrec l (CPPBinary o1 CPPOpLe   o2) = prio 20 l $ (prettyPrec 20 o1) <> text "<"  <> (prettyPrec 21 o2)
  prettyPrec l (CPPBinary o1 CPPOpGr   o2) = prio 20 l $ (prettyPrec 20 o1) <> text ">"  <> (prettyPrec 21 o2)
  prettyPrec l (CPPBinary o1 CPPOpGeq  o2) = prio 20 l $ (prettyPrec 20 o1) <> text ">=" <> (prettyPrec 21 o2)
  prettyPrec l (CPPBinary o1 CPPOpLeq  o2) = prio 20 l $ (prettyPrec 20 o1) <> text "<=" <> (prettyPrec 21 o2)
  prettyPrec l (CPPBinary o1 CPPOpEq   o2) = prio 18 l $ (prettyPrec 18 o1) <> text "==" <> (prettyPrec 19 o2)
  prettyPrec l (CPPBinary o1 CPPOpNeq  o2) = prio 18 l $ (prettyPrec 18 o1) <> text "!=" <> (prettyPrec 19 o2)
  prettyPrec l (CPPBinary o1 CPPOpAnd  o2) = prio 16 l $ (prettyPrec 16 o1) <> text "&"  <> (prettyPrec 16 o2)
  prettyPrec l (CPPBinary o1 CPPOpXor  o2) = prio 14 l $ (prettyPrec 14 o1) <> text "^"  <> (prettyPrec 14 o2)
  prettyPrec l (CPPBinary o1 CPPOpOr   o2) = prio 12 l $ (prettyPrec 12 o1) <> text "|"  <> (prettyPrec 12 o2)
  prettyPrec l (CPPBinary o1 CPPOpLAnd o2) = prio 10 l $ (prettyPrec 10 o1) <> text "&&" <> (prettyPrec 10 o2)
  prettyPrec l (CPPBinary o1 CPPOpLOr  o2) = prio  8 l $ (prettyPrec  8 o1) <> text "||" <> (prettyPrec 8  o2)
  prettyPrec l (CPPUnary  CPPOpPreInc o)   = prio 28 l $                       text "++" <> (prettyPrec 28 o )
  prettyPrec l (CPPUnary  CPPOpPreDec o)   = prio 28 l $                       text "--" <> (prettyPrec 28 o )
  prettyPrec l (CPPUnary  CPPOpPostInc o)  = prio 28 l $ (prettyPrec 28 o ) <> text "++"
  prettyPrec l (CPPUnary  CPPOpPostDec o)  = prio 28 l $ (prettyPrec 28 o ) <> text "--"
  prettyPrec l (CPPUnary  CPPOpAdr o)      = prio 28 l $                       text "&"  <> (prettyPrec 28 o )
  prettyPrec l (CPPUnary  CPPOpInd o)      = prio 28 l $                       text "*"  <> (prettyPrec 28 o )
  prettyPrec l (CPPUnary  CPPOpPlus o)     = prio 28 l $                       text "+"  <> (prettyPrec 28 o )
  prettyPrec l (CPPUnary  CPPOpMinus o)    = prio 28 l $                       text "-"  <> (prettyPrec 28 o )
  prettyPrec l (CPPUnary  CPPOpComp o)     = prio 28 l $                       text "~"  <> (prettyPrec 28 o )
  prettyPrec l (CPPUnary  CPPOpNeg o)      = prio 28 l $                       text "!"  <> (prettyPrec 28 o )
  prettyPrec l (CPPCond c (Just t) f)      = prio  6 l $ (prettyPrec 7  c ) <+> text "?"  <+> (prettyPrec 7  t ) <+> text ":" <+> (prettyPrec 6 f)
  prettyPrec l (CPPCond c Nothing t)       = prio  6 l $ (prettyPrec 7  c ) <> text "?:" <> (prettyPrec 6  t )
  prettyPrec l (CPPCast t e)               = prio 28 l $ lparen <> (pretty t) <> rparen <>  (prettyPrec 28 e )
  prettyPrec l (CPPSizeOfExpr e)           = prio 28 l $ text "sizeof" <> lparen <> (pretty e) <> rparen
  prettyPrec l (CPPSizeOfType t)           = prio 28 l $ text "sizeof" <> lparen <> (pretty t) <> rparen
  prettyPrec l (CPPIndex a b)              = prio 28 l $ (prettyPrec 28 a) <> lbrack <> (pretty b) <> rbrack
  prettyPrec l (CPPCall a b)               = prio 28 l $ (prettyPrec 28 a) <> lparen <> (hcat $ punctuate comma $ map pretty b) <> rparen
  prettyPrec l (CPPMember a m False)       = prio 28 l $ (prettyPrec 28 a) <> text "." <> text m
  prettyPrec l (CPPMember a m True)        = prio 28 l $ (prettyPrec 28 a) <> text "->" <> text m
  prettyPrec l (CPPNew a b)                = prio 28 l $ text "new" <+> (pretty a) <> lparen <> (hcat $ punctuate comma $ map pretty b) <> rparen

instance Pretty s => Pretty (Maybe s) where
  prettyPrec _ Nothing = empty
  prettyPrec l (Just x) = prettyPrec l x

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  prettyPrec l (Left x) = prettyPrec l x
  prettyPrec l (Right x) = prettyPrec l x

instance Pretty CPPStat where
  pretty (CPPLabel s b) = (nest (-1000) $ (text s) <> char ':') $$ pretty b
  pretty (CPPCase x b) = (text "case" <+> pretty x <> char ':') $+$ (nest 2 (pretty b))
  pretty (CPPDefault b) = (text "default:") $+$ (nest 2 $ pretty b)
  pretty (CPPSimple x) = (pretty x) <> char ';'
  pretty (CPPCompound []) = empty
  pretty (CPPCompound [CPPStatement (c@(CPPCompound _))]) = pretty c
  pretty (CPPCompound [CPPStatement (c@(CPPVerbStat _))]) = pretty c
  pretty (CPPCompound [CPPStatement a]) = pretty a
  pretty (CPPCompound l) = lbrace $+$ (nest 2 $ vcat $ map pretty l) $+$ rbrace
  pretty (CPPIf c t (Just f)) = text "if" <+> parens (pretty c) <+> braces (pretty t) <+> text "else" <+> braces (pretty f)
  pretty (CPPIf c t Nothing) = text "if" <+> parens (pretty c) <+> braces (pretty t)
  pretty (CPPSwitch x b) = text "switch (" <> pretty x <> text ") {" <+> pretty b <+> text "}"
  pretty (CPPWhile x False b) = text "while" <> (parens $ pretty x) <+> (braces $ pretty b)
  pretty (CPPWhile x True b) = text "do" <+> (braces $ pretty b) <+> text "while" <> (parens $ pretty x) <> semi
  pretty (CPPFor f1 f2 f3 b) = text "for (" <> pretty f1 <> text ";" <+> pretty f2 <> text ";" <+> pretty f3 <> text ") {" $+$ nest 2 (pretty b) $+$ text "}"
  pretty (CPPGoto l) = text ("goto " ++ l ++ ";")
  pretty (CPPCont) = text "continue;"
  pretty (CPPBreak) = text "break;"
  pretty (CPPReturn x) = (text "return" <+> pretty x) <> text ";"
  pretty (CPPDelete x) = (text "delete" <+> pretty x) <> text ";"
  pretty (CPPVerbStat l) = lbrace $+$ (nest 2 $ vcat $ map text l) $+$ rbrace

instance Pretty CPPQual where
  pretty (CPPQualConst) = text "const"
  pretty (CPPQualVolatile) = text "volatile"

instance Pretty CPPStorSpec where
  pretty (CPPAuto) = text "auto"
  pretty (CPPRegister) = text "register"
  pretty (CPPStatic) = text "static"
  pretty (CPPExtern) = text "extern"
  pretty (CPPTypedef) = text "typedef"
  pretty (CPPInline) = text "inline"
  pretty (CPPVirtual) = text "virtual"

instance Pretty a => Pretty [a] where
  pretty [] = empty
  pretty [a] = pretty a
  pretty (a:b) = pretty a <+> pretty b

instance Pretty CPPVisibility where
  pretty CPPPublic = text "public"
  pretty CPPPrivate = text "private"
  pretty CPPProtected = text "protected"

instance Pretty (CPPType,Doc,Int,[CPPQual]) where
  pretty (CPPPtr qual typ,s,l,q) = pretty (typ,char '*' <> (pretty q <+> (prio 4 l s)),4::Int,qual)
  pretty (CPPRef qual typ,s,l,q) = pretty (typ,char '&' <> (pretty q <+> (prio 4 l s)),4::Int,qual)
  pretty (CPPArray qual typ len,s,l,_) = pretty (typ,((prio 2 l s) <> lbrack <> pretty len <> rbrack),2::Int,qual)
  pretty (CPPTypePrim prim,s,l,q) = pretty q <+> (text prim <+> s)
  pretty (CPPTempl prim lst,s,l,q) = pretty q <+> (text prim <> char '<' <> (hcat $ punctuate comma $ map pretty lst) <> char '>') <+> s

instance Pretty (CPPType,Doc) where
  pretty (typ,doc) = pretty (typ,doc,0 :: Int,[]::[CPPQual])

instance Pretty CPPType where
  pretty x = pretty (x,empty)

prettyString Nothing = empty
prettyString (Just x) = text x

instance Pretty CPPDecl where
  pretty (CPPDecl { cppDeclName=name, cppType = typ, cppTypeQual = qual, cppTypeStor = stor, cppDeclInit=Nothing }) = pretty stor <+> pretty (typ,prettyString name,0 :: Int,qual)
  pretty (CPPDecl { cppDeclName=name, cppType = typ, cppTypeQual = qual, cppTypeStor = stor, cppDeclInit=Just (CPPInitValue code) }) = pretty stor <+> pretty (typ,prettyString name,0 :: Int,qual) <> char '=' <> pretty code
  pretty (CPPDecl { cppDeclName=name, cppType = typ, cppTypeQual = qual, cppTypeStor = stor, cppDeclInit=Just (CPPInitCall  args) }) = pretty stor <+> pretty (typ,prettyString name,0 :: Int,qual) <> lparen <> (hcat $ punctuate comma $ map pretty args) <> rparen
  pretty (CPPDecl { cppDeclName=name, cppType = typ, cppTypeQual = qual, cppTypeStor = stor, cppDeclInit=Just (CPPInitArray args) }) = pretty stor <+> pretty (typ,prettyString name,0 :: Int,qual) <> char '=' <> lbrace <> (hcat $ punctuate comma $ map pretty args) <> rbrace

instance Pretty CPPDef where
  pretty (CPPDef { cppDefName=name, cppDefRetType=typ, cppDefStor=stor, cppDefArgs=args, cppDefBody = body, cppDefQual=qual }) =
    let pre = (pretty stor <+> pretty (typ, text name)) <> parens (hcat $ punctuate comma $ map pretty args) <+> (hsep $ map pretty qual)
        in case body of
          Nothing -> pre <> text ";"
          Just b -> pre <+> text "{" $+$ (nest 2 $ pretty b) $+$ text "}"

instance Pretty (CPPConstr,String) where
  pretty (CPPConstr { cppConstrStor=stor, cppConstrArgs=args, cppConstrBody=body, cppConstrInit=ini },name) =
    let pre = (pretty stor <+> text name) <> parens (hcat $ punctuate comma $ map pretty args)
        init [] = empty
        init lst = colon <+> (hcat $ punctuate (text ", ") $ map (\(tp,args) -> pretty tp <> (parens $ hcat $ punctuate comma $ map pretty args)) lst)
        in case body of
          Nothing -> (pre <+> init ini) <> text ";"
          Just b -> (pre <+> init ini) <+> text "{" $+$ (nest 2 $ pretty b) $+$ text "}"

instance Pretty CPPBlockItem where
  pretty (CPPStatement stat) = pretty stat
  pretty (CPPBlockDecl decl) = pretty decl <> text ";"
  pretty (CPPComment str) = text "//" <+> text str

instance Pretty CPPMacroStm where
  pretty (CPPMacroIncludeUser str) = text "#include" <+> (text $ "\"" ++ str ++"\"")
  pretty (CPPMacroIncludeSys str)  = text "#include" <+> (text $ "<" ++ str ++ ">")
  pretty (CPPMacroDefine { cppMacroDefName = name, cppMacroDefArgs = Nothing, cppMacroDefExpr = expr }) = text "#define" <+> text name <+> text expr
  pretty (CPPMacroDefine { cppMacroDefName = name, cppMacroDefArgs = Just lst, cppMacroDefExpr = expr }) = text $ "#define " ++ name ++ "(" ++ (foldr1 (\a b -> a++","++b) lst) ++ ")" ++ " " ++ expr

instance Pretty CPPElement where
  pretty (CPPElemNamespace (name,ns)) = (text "namespace" <+> text name <+> lbrace) $+$ nest 2 (pretty ns) $+$ rbrace
  pretty (CPPElemDecl decl) = pretty decl <> semi
  pretty (CPPElemDef def) = pretty def
  pretty (CPPElemClass cls) = pretty cls

instance Pretty CPPNamespace where
  pretty (CPPNamespace list) = vcat $ map (\x -> pretty x $+$ char ' ') list

instance Pretty CPPClass where
  pretty (CPPClass { cppClassName = name, cppClassInherit = inh, cppClassDecls = decls, cppClassDefs = defs, cppClassConstrs = constrs }) = 
    let sel vis lst = map snd $ filter (\x -> fst x == vis) lst
        inhh [] = empty
        inhh lst = colon <+> (hcat $ punctuate (text ", ") $ map (\(vis,tp) -> pretty vis <+> pretty tp) lst)
        decl vis = case sel vis decls of
          [] -> empty
          lst -> (nest (-2) (pretty vis) <> char ':') $+$ vcat (map (\x -> pretty x <> semi) lst) $+$ text " "
        def vis = case sel vis defs of
          [] -> empty
          lst -> (nest (-2) (pretty vis) <> char ':') $+$ vcat (map pretty lst) $+$ text " "
        constr vis = case sel vis constrs of
          [] -> empty
          lst -> (nest (-2) (pretty vis) <> char ':') $+$ vcat (map (\x -> pretty (x,name)) lst) $+$ text " "
        comb vis = constr vis $+$ def vis
        in (text "class" <+> text name <+> inhh inh <+> char '{') $+$ nest 2 (decl CPPPrivate $+$ decl CPPProtected $+$ decl CPPPublic $+$ comb CPPPrivate $+$ comb CPPProtected $+$ comb CPPPublic) $+$ char '}' <> semi

instance Pretty CPPFile where
  pretty (CPPFile { cppMacroStm = macro, cppUsing = using, cppTranslUnit = unit }) = vcat (map pretty macro) $+$ text " " $+$ vcat (map (\x -> text "using" <+> text "namespace" <+> text x <> semi) using) $+$ text " " $+$ pretty unit

codegen :: Pretty x => x -> String
codegen = render . pretty
