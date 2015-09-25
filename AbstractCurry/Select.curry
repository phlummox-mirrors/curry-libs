------------------------------------------------------------------------
--- This library provides some useful operations to select components
--- in AbstractCurry programs, i.e., it provides a collection of
--- selector functions for AbstractCurry.
---
--- @version September 2015
--- @category meta
------------------------------------------------------------------------

module AbstractCurry.Select where
--     ( imports, functions, constructors, types, publicFuncNames
--     , publicConsNames, publicTypeNames
--
--     , typeName, typeVis, typeCons
--     , consName, consVis
--     , isBaseType, isPolyType, isFunctionalType, isIOType, isIOReturnType
--     , argTypes, resultType, tvarsOfType, modsOfType
--
--     , funcName, funcVis
--
--     , varsOfPat, varsOfExp, varsOfRhs, varsOfStat, varsOfLDecl
--     , varsOfFDecl, varsOfRule
--
--     , isPrelude) where

import AbstractCurry.Types
import List(union)

------------------------------------------------------------------------
-- Selectors for curry programs

--- Returns the imports (module names) of a given curry program.
imports :: CurryProg -> [MName]
imports (CurryProg _ ms _ _ _) = ms

--- Returns the function declarations of a given curry program.
functions :: CurryProg -> [CFuncDecl]
functions (CurryProg _ _ _ fs _) = fs

--- Returns all constructors of given curry program.
constructors :: CurryProg -> [CConsDecl]
constructors = concatMap typeCons . types

--- Returns the type declarations of a given curry program.
types :: CurryProg -> [CTypeDecl]
types (CurryProg _ _ ts _ _) = ts

--- Returns the names of all visible functions in given curry program.
publicFuncNames :: CurryProg -> [QName]
publicFuncNames = map funcName . filter ((== Public) . funcVis) . functions

--- Returns the names of all visible constructors in given curry program.
publicConsNames :: CurryProg -> [QName]
publicConsNames = map consName
                . filter ((== Public) . consVis)
                . constructors

--- Returns the names of all visible types in given curry program.
publicTypeNames :: CurryProg -> [QName]
publicTypeNames = map typeName . filter ((== Public) . typeVis) . types

------------------------------------------------------------------------
-- Selectors for type expressions

--- Returns the name of a given type declaration
typeName :: CTypeDecl -> QName
typeName (CType    n _ _ _) = n
typeName (CTypeSyn n _ _ _) = n
typeName (CNewType n _ _ _) = n

--- Returns the visibility of a given type declaration
typeVis :: CTypeDecl -> CVisibility
typeVis (CType    _ vis _ _) = vis
typeVis (CTypeSyn _ vis _ _) = vis
typeVis (CNewType _ vis _ _) = vis

--- Returns the constructors of a given type declaration.
typeCons :: CTypeDecl -> [CConsDecl]
typeCons (CType    _ _ _ cs) = cs
typeCons (CTypeSyn _ _ _ _ ) = []
typeCons (CNewType _ _ _ c ) = [c]

--- Returns the name of a given constructor declaration.
consName :: CConsDecl -> QName
consName (CCons   n _ _) = n
consName (CRecord n _ _) = n

--- Returns the visibility of a given constructor declaration.
consVis :: CConsDecl -> CVisibility
consVis (CCons   _ vis _) = vis
consVis (CRecord _ vis _) = vis

--- Returns true if the type expression is a base type.
isBaseType :: CTypeExpr -> Bool
isBaseType texp = case texp of
  CTCons _ args -> null args
  _             -> False

--- Returns true if the type expression contains type variables.
isPolyType :: CTypeExpr -> Bool
isPolyType (CTVar                _) = True
isPolyType (CFuncType domain range) = isPolyType domain || isPolyType range
isPolyType (CTCons      _ typelist) = any isPolyType typelist

--- Returns true if the type expression is a functional type.
isFunctionalType :: CTypeExpr -> Bool
isFunctionalType texp = case texp of
  CFuncType _ _ -> True
  _             -> False

--- Returns true if the type expression is (IO t).
isIOType :: CTypeExpr -> Bool
isIOType texp = case texp of
  CTCons tc _ -> tc == pre "IO"
  _           -> False

--- Returns true if the type expression is (IO t) with t/=() and
--- t is not functional
isIOReturnType :: CTypeExpr -> Bool
isIOReturnType (CTVar            _) = False
isIOReturnType (CFuncType      _ _) = False
isIOReturnType (CTCons tc typelist) =
  tc==pre "IO" && head typelist /= CTCons (pre "()") []
  && not (isFunctionalType (head typelist))

--- Returns all argument types from a functional type
argTypes :: CTypeExpr -> [CTypeExpr]
argTypes (CTVar         _) = []
argTypes (CTCons      _ _) = []
argTypes (CFuncType t1 t2) = t1 : argTypes t2

--- Return the result type from a (nested) functional type
resultType :: CTypeExpr -> CTypeExpr
resultType (CTVar          n) = CTVar n
resultType (CTCons name args) = CTCons name args
resultType (CFuncType   _ t2) = resultType t2

--- Returns all type variables occurring in a type expression.
tvarsOfType :: CTypeExpr -> [CTVarIName]
tvarsOfType (CTVar v) = [v]
tvarsOfType (CFuncType t1 t2) = tvarsOfType t1 ++ tvarsOfType t2
tvarsOfType (CTCons _ args) = concatMap tvarsOfType args

--- Returns all modules used in the given type.
modsOfType :: CTypeExpr -> [String]
modsOfType (CTVar            _) = []
modsOfType (CFuncType    t1 t2) = modsOfType t1 `union` modsOfType t2
modsOfType (CTCons (mod,_) tys) = foldr union [mod] $ map modsOfType tys

------------------------------------------------------------------------
-- Selectors for function definitions

--- Returns the name of a given function declaration
funcName :: CFuncDecl -> QName
funcName (CFunc     n _ _ _ _) = n
funcName (CmtFunc _ n _ _ _ _) = n

--- Returns the visibility of a given function declaration
funcVis :: CFuncDecl -> CVisibility
funcVis (CFunc     _ _ vis _ _) = vis
funcVis (CmtFunc _ _ _ vis _ _) = vis

------------------------------------------------------------------------
-- Operations to compute the variables occurring in a pattern or expression:

--- Returns list of all variables occurring in a pattern.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfPat :: CPattern -> [CVarIName]
varsOfPat (CPVar v) = [v]
varsOfPat (CPLit _) = []
varsOfPat (CPComb _ pats) = concatMap varsOfPat pats
varsOfPat (CPAs v pat) = v : varsOfPat pat
varsOfPat (CPFuncComb _ pats) = concatMap varsOfPat pats
varsOfPat (CPLazy pat) = varsOfPat pat
varsOfPat (CPRecord _ recpats) = concatMap (varsOfPat . snd) recpats

--- Returns list of all variables occurring in an expression.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfExp :: CExpr -> [CVarIName]
varsOfExp (CVar v)            = [v]
varsOfExp (CLit _)            = []
varsOfExp (CSymbol _)         = []
varsOfExp (CApply e1 e2)      = varsOfExp e1 ++ varsOfExp e2
varsOfExp (CLambda pl le)     = concatMap varsOfPat pl ++ varsOfExp le
varsOfExp (CLetDecl ld le)    = concatMap varsOfLDecl ld ++ varsOfExp le
varsOfExp (CDoExpr sl)        = concatMap varsOfStat sl
varsOfExp (CListComp le sl)   = varsOfExp le ++ concatMap varsOfStat sl
varsOfExp (CCase _ ce bl)     =
  varsOfExp ce ++ concatMap (\ (p,rhs) -> varsOfPat p ++ varsOfRhs rhs) bl
varsOfExp (CTyped te _)       = varsOfExp te
varsOfExp (CRecConstr _ upds) = concatMap (varsOfExp . snd) upds
varsOfExp (CRecUpdate e upds) = varsOfExp e ++ concatMap (varsOfExp . snd) upds

--- Returns list of all variables occurring in a right-hand side.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfRhs :: CRhs -> [CVarIName]
varsOfRhs (CSimpleRhs rhs ldecls) =
  varsOfExp rhs ++ concatMap varsOfLDecl ldecls
varsOfRhs (CGuardedRhs gs  ldecls) =
  concatMap (\ (g,e) -> varsOfExp g ++ varsOfExp e) gs  ++
  concatMap varsOfLDecl ldecls

--- Returns list of all variables occurring in a statement.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfStat :: CStatement -> [CVarIName]
varsOfStat (CSExpr e)  = varsOfExp e
varsOfStat (CSPat p e) = varsOfPat p ++ varsOfExp e
varsOfStat (CSLet ld)  = concatMap varsOfLDecl ld

--- Returns list of all variables occurring in a local declaration.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfLDecl :: CLocalDecl -> [CVarIName]
varsOfLDecl (CLocalFunc f)     = varsOfFDecl f
varsOfLDecl (CLocalPat p rhs)  = varsOfPat p ++ varsOfRhs rhs
varsOfLDecl (CLocalVars lvars) = lvars

--- Returns list of all variables occurring in a function declaration.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfFDecl :: CFuncDecl -> [CVarIName]
varsOfFDecl (CFunc     _ _ _ _ r) = concatMap varsOfRule r
varsOfFDecl (CmtFunc _ _ _ _ _ r) = concatMap varsOfRule r

--- Returns list of all variables occurring in a rule.
--- Each occurrence corresponds to one element, i.e., the list might
--- contain multiple elements.
varsOfRule :: CRule -> [CVarIName]
varsOfRule (CRule pats rhs) = concatMap varsOfPat pats ++ varsOfRhs rhs



funcNamesOfLDecl :: CLocalDecl -> [QName]
funcNamesOfLDecl lDecl =
    case lDecl of CLocalFunc f -> funcNamesOfFDecl f
                  _            -> []

funcNamesOfFDecl :: CFuncDecl -> [QName]
funcNamesOfFDecl (CFunc     qn _ _ _ _) = [qn]
funcNamesOfFDecl (CmtFunc _ qn _ _ _ _) = [qn]

funcNamesOfStat :: CStatement -> [QName]
funcNamesOfStat stms =
    case stms of CSLet ld -> concatMap funcNamesOfLDecl ld
                 _        -> []

------------------------------------------------------------------------
--- Tests whether a module name is the prelude.
isPrelude :: String -> Bool
isPrelude m = m == "Prelude"

------------------------------------------------------------------------
