-- editorconfig-checker-disable-file
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlutusCore.MkPlc
    ( TermLike (..)
    , UniOf
    , mkTyBuiltinOf
    , mkTyBuiltin
    , mkConstantOf
    , mkConstant
    , VarDecl (..)
    , TyVarDecl (..)
    , TyDecl (..)
    , mkVar
    , mkTyVar
    , tyDeclVar
    , Def (..)
    , embed
    , TermDef
    , TypeDef
    , FunctionType (..)
    , FunctionDef (..)
    , functionTypeToType
    , functionDefToType
    , functionDefVarDecl
    , mkFunctionDef
    , mkImmediateLamAbs
    , mkImmediateTyAbs
    , mkIterTyForall
    , mkIterTyLam
    , mkIterApp
    , mkMultiApp
    , mkIterTyFun
    , mkIterLamAbs
    , mkMultiLamAbs
    , mkIterInst
    , mkIterTyAbs
    , mkIterTyApp
    , mkIterKindArrow
    ) where

import Data.List.NonEmpty qualified as NE
import PlutusPrelude
import Prelude hiding (error)

import PlutusCore.Core.Type

import Universe

-- | A final encoding for Term, to allow PLC terms to be used transparently as PIR terms.
class TermLike term tyname name uni fun | term -> tyname name uni fun where
    var      :: ann -> name -> term ann
    tyAbs    :: ann -> tyname -> Kind ann -> term ann -> term ann
    lamAbs   :: ann -> name -> Type tyname uni ann -> term ann -> term ann
    multiLamAbs   :: ann -> NE.NonEmpty (name, Type tyname uni ann) -> term ann -> term ann
    apply    :: ann -> term ann -> term ann -> term ann
    multiApply    :: ann -> term ann -> NE.NonEmpty (term ann) -> term ann
    constant :: ann -> Some (ValueOf uni) -> term ann
    builtin  :: ann -> fun -> term ann
    tyInst   :: ann -> term ann -> Type tyname uni ann -> term ann
    unwrap   :: ann -> term ann -> term ann
    iWrap    :: ann -> Type tyname uni ann -> Type tyname uni ann -> term ann -> term ann
    error    :: ann -> Type tyname uni ann -> term ann
    constr   :: ann -> Type tyname uni ann -> Int -> [term ann] -> term ann
    kase     :: ann -> Type tyname uni ann -> term ann -> [term ann] -> term ann

    termLet  :: ann -> TermDef term tyname name uni ann -> term ann -> term ann
    typeLet  :: ann -> TypeDef tyname uni ann -> term ann -> term ann

    termLet = mkImmediateLamAbs
    typeLet = mkImmediateTyAbs

-- TODO: make it @forall {k}@ once we have that.
-- (see https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0099-explicit-specificity.rst)
-- | Embed a type (given its explicit type tag) into a PLC type.
mkTyBuiltinOf :: forall k (a :: k) uni tyname ann. ann -> uni (Esc a) -> Type tyname uni ann
mkTyBuiltinOf ann = TyBuiltin ann . SomeTypeIn

-- TODO: make it @forall {k}@ once we have that.
-- (see https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0099-explicit-specificity.rst)
-- | Embed a type (provided it's in the universe) into a PLC type.
mkTyBuiltin
    :: forall k (a :: k) uni tyname ann. uni `Contains` a
    => ann -> Type tyname uni ann
mkTyBuiltin ann = mkTyBuiltinOf ann $ knownUni @_ @uni @a

-- | Embed a Haskell value (given its explicit type tag) into a PLC term.
mkConstantOf
    :: forall a uni fun term tyname name ann. TermLike term tyname name uni fun
    => ann -> uni (Esc a) -> a -> term ann
mkConstantOf ann uni = constant ann . someValueOf uni

-- | Embed a Haskell value (provided its type is in the universe) into a PLC term.
mkConstant
    :: forall a uni fun term tyname name ann. (TermLike term tyname name uni fun, uni `Includes` a)
    => ann -> a -> term ann
mkConstant ann = constant ann . someValue

instance TermLike (Term tyname name uni fun) tyname name uni fun where
    var      = Var
    tyAbs    = TyAbs
    lamAbs a n ty = LamAbs a (NE.singleton (n, ty))
    multiLamAbs   = LamAbs
    apply a f arg = Apply a f (NE.singleton arg)
    multiApply    = Apply
    constant = Constant
    builtin  = Builtin
    tyInst   = TyInst
    unwrap   = Unwrap
    iWrap    = IWrap
    error    = Error
    constr   = Constr
    kase     = Case

embed :: TermLike term tyname name uni fun => Term tyname name uni fun ann -> term ann
embed = \case
    Var a n           -> var a n
    TyAbs a tn k t    -> tyAbs a tn k (embed t)
    LamAbs a vars t   -> multiLamAbs a vars (embed t)
    Apply a t1 t2     -> multiApply a (embed t1) (fmap embed t2)
    Constant a c      -> constant a c
    Builtin a bi      -> builtin a bi
    TyInst a t ty     -> tyInst a (embed t) ty
    Error a ty        -> error a ty
    Unwrap a t        -> unwrap a (embed t)
    IWrap a ty1 ty2 t -> iWrap a ty1 ty2 (embed t)
    Constr a ty i es  -> constr a ty i (fmap embed es)
    Case a ty arg cs  -> kase a ty (embed arg) (fmap embed cs)

-- | Make a 'Var' referencing the given 'VarDecl'.
mkVar :: TermLike term tyname name uni fun => ann -> VarDecl tyname name uni ann -> term ann
mkVar ann = var ann . _varDeclName

-- | Make a 'TyVar' referencing the given 'TyVarDecl'.
mkTyVar :: ann -> TyVarDecl tyname ann -> Type tyname uni ann
mkTyVar ann = TyVar ann . _tyVarDeclName

-- | A definition. Pretty much just a pair with more descriptive names.
data Def var val = Def
    { defVar :: var
    , defVal :: val
    } deriving stock (Show, Eq, Ord, Generic)

-- | A term definition as a variable.
type TermDef term tyname name uni ann = Def (VarDecl tyname name uni ann) (term ann)
-- | A type definition as a type variable.
type TypeDef tyname uni ann = Def (TyVarDecl tyname ann) (Type tyname uni ann)

-- | The type of a PLC function.
data FunctionType tyname uni ann = FunctionType
    { _functionTypeAnn :: ann                  -- ^ An annotation.
    , _functionTypeDom :: Type tyname uni ann  -- ^ The domain of a function.
    , _functionTypeCod :: Type tyname uni ann  -- ^ The codomain of the function.
    }

-- Should we parameterize 'VarDecl' by @ty@ rather than @tyname@, so that we can define
-- 'FunctionDef' as 'TermDef FunctionType tyname name uni fun ann'?
-- Perhaps we even should define general 'Decl' and 'Def' that cover all of the cases?
-- | A PLC function.
data FunctionDef term tyname name uni fun ann = FunctionDef
    { _functionDefAnn  :: ann                          -- ^ An annotation.
    , _functionDefName :: name                         -- ^ The name of a function.
    , _functionDefType :: FunctionType tyname uni ann  -- ^ The type of the function.
    , _functionDefTerm :: term ann                     -- ^ The definition of the function.
    }

-- | Convert a 'FunctionType' to the corresponding 'Type'.
functionTypeToType :: FunctionType tyname uni ann -> Type tyname uni ann
functionTypeToType (FunctionType ann dom cod) = TyFun ann dom cod

-- | Get the type of a 'FunctionDef'.
functionDefToType :: FunctionDef term tyname name uni fun ann -> Type tyname uni ann
functionDefToType (FunctionDef _ _ funTy _) = functionTypeToType funTy

-- | Convert a 'FunctionDef' to a 'VarDecl'. I.e. ignore the actual term.
functionDefVarDecl :: FunctionDef term tyname name uni fun ann -> VarDecl tyname name uni ann
functionDefVarDecl (FunctionDef ann name funTy _) = VarDecl ann name $ functionTypeToType funTy

-- | Make a 'FunctionDef'. Return 'Nothing' if the provided type is not functional.
mkFunctionDef
    :: ann
    -> name
    -> Type tyname uni ann
    -> term ann
    -> Maybe (FunctionDef term tyname name uni fun ann)
mkFunctionDef annName name (TyFun annTy dom cod) term =
    Just $ FunctionDef annName name (FunctionType annTy dom cod) term
mkFunctionDef _       _    _                     _    = Nothing

-- | Make a "let-binding" for a term as an immediately applied lambda abstraction.
mkImmediateLamAbs
    :: TermLike term tyname name uni fun
    => ann
    -> TermDef term tyname name uni ann
    -> term ann -- ^ The body of the let, possibly referencing the name.
    -> term ann
mkImmediateLamAbs ann1 (Def (VarDecl ann2 name ty) bind) body =
    apply ann1 (lamAbs ann2 name ty body) bind

-- | Make a "let-binding" for a type as an immediately instantiated type abstraction. Note: the body must be a value.
mkImmediateTyAbs
    :: TermLike term tyname name uni fun
    => ann
    -> TypeDef tyname uni ann
    -> term ann -- ^ The body of the let, possibly referencing the name.
    -> term ann
mkImmediateTyAbs ann1 (Def (TyVarDecl ann2 name k) bind) body =
    tyInst ann1 (tyAbs ann2 name k body) bind

-- | Make an iterated application.
mkIterApp
    :: TermLike term tyname name uni fun
    => ann
    -> term ann -- ^ @f@
    -> [term ann] -- ^@[ x0 ... xn ]@
    -> term ann -- ^ @[f x0 ... xn ]@
mkIterApp ann = foldl' (apply ann)

-- | Make an iterated application.
mkMultiApp
    :: TermLike term tyname name uni fun
    => ann
    -> term ann -- ^ @f@
    -> [term ann] -- ^@[ x0 ... xn ]@
    -> term ann -- ^ @[f x0 ... xn ]@
mkMultiApp ann fun args = case NE.nonEmpty args of
    Just args' -> multiApply ann fun args'
    Nothing    -> fun

-- | Make an iterated instantiation.
mkIterInst
    :: TermLike term tyname name uni fun
    => ann
    -> term ann -- ^ @a@
    -> [Type tyname uni ann] -- ^ @ [ x0 ... xn ] @
    -> term ann -- ^ @{ a x0 ... xn }@
mkIterInst ann = foldl' (tyInst ann)

-- | Lambda abstract a list of names.
mkIterLamAbs
    :: TermLike term tyname name uni fun
    => [VarDecl tyname name uni ann]
    -> term ann
    -> term ann
mkIterLamAbs args body =
    foldr (\(VarDecl ann name ty) acc -> lamAbs ann name ty acc) body args

-- | Lambda abstract a list of names.
mkMultiLamAbs
    :: TermLike term tyname name uni fun
    => [VarDecl tyname name uni ann]
    -> term ann
    -> term ann
mkMultiLamAbs args body = case NE.nonEmpty args of
    Just vds ->
        let
            ann = _varDeclAnn $ NE.head vds
            vars = fmap (\(VarDecl _ n ty) -> (n, ty)) vds
        in multiLamAbs ann vars body
    Nothing -> body

-- | Type abstract a list of names.
mkIterTyAbs
    :: TermLike term tyname name uni fun
    => [TyVarDecl tyname ann]
    -> term ann
    -> term ann
mkIterTyAbs args body =
    foldr (\(TyVarDecl ann name kind) acc -> tyAbs ann name kind acc) body args

-- | Make an iterated type application.
mkIterTyApp
    :: ann
    -> Type tyname uni ann -- ^ @f@
    -> [Type tyname uni ann] -- ^ @[ x0 ... xn ]@
    -> Type tyname uni ann -- ^ @[ f x0 ... xn ]@
mkIterTyApp ann = foldl' (TyApp ann)

-- | Make an iterated function type.
mkIterTyFun
    :: ann
    -> [Type tyname uni ann]
    -> Type tyname uni ann
    -> Type tyname uni ann
mkIterTyFun ann tys target = foldr (\ty acc -> TyFun ann ty acc) target tys

-- | Universally quantify a list of names.
mkIterTyForall
    :: [TyVarDecl tyname ann]
    -> Type tyname uni ann
    -> Type tyname uni ann
mkIterTyForall args body =
    foldr (\(TyVarDecl ann name kind) acc -> TyForall ann name kind acc) body args

-- | Lambda abstract a list of names.
mkIterTyLam
    :: [TyVarDecl tyname ann]
    -> Type tyname uni ann
    -> Type tyname uni ann
mkIterTyLam args body =
    foldr (\(TyVarDecl ann name kind) acc -> TyLam ann name kind acc) body args

-- | Make an iterated function kind.
mkIterKindArrow
    :: ann
    -> [Kind ann]
    -> Kind ann
    -> Kind ann
mkIterKindArrow ann kinds target = foldr (KindArrow ann) target kinds
