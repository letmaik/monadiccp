-- AST for C++ code

{- based on:
   language-c-0.3.1.1: Analysis and generation of C code
   Language.C.Syntax.AST

   Abstract syntax of C++ source and header files.
-}

module Language.CPP.Syntax.AST where

data CPPFile = CPPFile { cppMacroStm :: [CPPMacroStm], cppUsing :: [String], cppTranslUnit :: CPPNamespace }
  deriving (Eq,Ord,Show)

data CPPMacroStm = 
    CPPMacroIncludeUser String
  | CPPMacroIncludeSys String
  | CPPMacroDefine { cppMacroDefName:: String, cppMacroDefArgs :: Maybe [String], cppMacroDefExpr :: String }
  deriving (Eq,Ord,Show)

data CPPElement =
    CPPElemNamespace (String,CPPNamespace)
  | CPPElemDecl CPPDecl
  | CPPElemDef CPPDef
  | CPPElemClass CPPClass
  deriving (Eq,Ord,Show)

data CPPNamespace = CPPNamespace [CPPElement]
  deriving (Eq,Ord,Show)

data CPPClass = CPPClass { cppClassName :: String, cppClassInherit :: [(CPPVisibility,CPPType)], cppClassDecls :: [(CPPVisibility,CPPDecl)], cppClassDefs :: [(CPPVisibility,CPPDef)], cppClassConstrs :: [(CPPVisibility,CPPConstr)] }
  deriving (Eq,Ord,Show)

data CPPVisibility =
    CPPPublic
  | CPPProtected
  | CPPPrivate
  deriving (Eq,Ord,Show)

-- TODO: function pointers
-- TODO: struct/union/enum
data CPPType =
    CPPTypePrim String
  | CPPArray [CPPQual] CPPType (Maybe CPPExpr)
  | CPPPtr [CPPQual] CPPType
  | CPPRef [CPPQual] CPPType
  | CPPTempl String [CPPType]
  deriving (Eq,Ord,Show)

data CPPStorSpec =
    CPPAuto
  | CPPRegister
  | CPPStatic
  | CPPExtern
  | CPPTypedef
  | CPPInline
  | CPPVirtual
  deriving (Eq,Ord,Show)

data CPPQual =
    CPPQualConst
  | CPPQualVolatile
  deriving (Eq,Ord,Show)

data CPPInit =
    CPPInitValue CPPExpr
  | CPPInitCall  [CPPExpr]
  | CPPInitArray [CPPExpr]
  deriving (Eq,Ord,Show)

data CPPDecl = CPPDecl { cppDeclName :: Maybe String, cppType :: CPPType, cppTypeQual :: [CPPQual], cppTypeStor :: [CPPStorSpec], cppDeclInit :: Maybe CPPInit }
  deriving (Eq,Ord,Show)

data CPPDef = CPPDef { cppDefName :: String, cppDefRetType :: CPPType, cppDefStor :: [CPPStorSpec], cppDefQual :: [CPPQual], cppDefArgs :: [CPPDecl], cppDefBody :: Maybe CPPStat }
  deriving (Eq,Ord,Show)

data CPPConstr = CPPConstr { cppConstrStor :: [CPPStorSpec], cppConstrArgs :: [CPPDecl], cppConstrBody :: Maybe CPPStat, cppConstrInit :: [(Either CPPExpr CPPType,[CPPExpr])] }
  deriving (Eq,Ord,Show)

data CPPStat = 
    CPPLabel String CPPStat
  | CPPCase CPPExpr CPPStat
  | CPPDefault CPPStat
  | CPPSimple CPPExpr
  | CPPCompound [CPPBlockItem]
  | CPPVerbStat [String]
  | CPPIf CPPExpr CPPStat (Maybe CPPStat)
  | CPPSwitch CPPExpr CPPStat
  | CPPWhile CPPExpr Bool CPPStat
  | CPPFor (Either (Maybe CPPExpr) CPPDecl) (Maybe CPPExpr) (Maybe CPPExpr) CPPStat
  | CPPGoto String
  | CPPCont
  | CPPBreak
  | CPPReturn (Maybe CPPExpr)
  | CPPDelete CPPExpr
  deriving (Eq,Ord,Show)

data CPPBlockItem =
    CPPStatement CPPStat
  | CPPBlockDecl CPPDecl
  | CPPComment String
  deriving (Eq,Ord,Show)

data CPPExpr =
    CPPComma [CPPExpr]
  | CPPAssign CPPExpr CPPAssignOp CPPExpr
  | CPPBinary CPPExpr CPPBinaryOp CPPExpr
  | CPPUnary CPPUnaryOp CPPExpr
  | CPPCond CPPExpr (Maybe CPPExpr) CPPExpr
  | CPPCast CPPType CPPExpr
  | CPPSizeOfExpr CPPExpr
  | CPPSizeOfType CPPType
  | CPPIndex CPPExpr CPPExpr
  | CPPCall CPPExpr [CPPExpr]
  | CPPMember CPPExpr String Bool
  | CPPVar String
  | CPPConst CPPConst
  | CPPNew CPPType [CPPExpr]
  deriving (Eq,Ord,Show)

data CPPConst =
    CPPConstInt Integer
  | CPPConstChar String
  | CPPConstFloat String
  | CPPConstString String
  deriving (Eq,Ord,Show)

data CPPAssignOp =
    CPPAssOp
  | CPPAssOpMul
  | CPPAssOpDiv
  | CPPAssOpRmd
  | CPPAssOpAdd
  | CPPAssOpSub
  | CPPAssOpShl
  | CPPAssOpShr
  | CPPAssOpAnd
  | CPPAssOpOr
  | CPPAssOpXor
  deriving (Eq,Ord,Show)

data CPPUnaryOp =
    CPPOpPreInc
  | CPPOpPostInc
  | CPPOpPreDec
  | CPPOpPostDec
  | CPPOpAdr
  | CPPOpInd
  | CPPOpPlus
  | CPPOpMinus
  | CPPOpComp
  | CPPOpNeg
  deriving (Eq,Ord,Show)

data CPPBinaryOp =
    CPPOpMul
  | CPPOpDiv
  | CPPOpRmd
  | CPPOpAdd
  | CPPOpSub
  | CPPOpShl
  | CPPOpShr
  | CPPOpLe
  | CPPOpGr
  | CPPOpLeq
  | CPPOpGeq
  | CPPOpEq
  | CPPOpNeq
  | CPPOpAnd
  | CPPOpOr
  | CPPOpXor
  | CPPOpLAnd
  | CPPOpLOr
  deriving (Eq,Ord,Show)
