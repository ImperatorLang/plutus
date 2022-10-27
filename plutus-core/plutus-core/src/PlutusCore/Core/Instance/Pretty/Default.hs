-- | While the flexible pretty-printing infrastructure is useful when you want it,
-- it's helpful to have an implementation of the default Pretty typeclass that
-- does the default thing.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusCore.Core.Instance.Pretty.Default () where

import PlutusPrelude

import PlutusCore.Core.Instance.Pretty.Classic ()
import PlutusCore.Core.Type
import PlutusCore.Pretty.Classic
import PlutusCore.Pretty.PrettyConst

import Universe

instance Pretty ann => Pretty (Kind ann) where
    pretty = prettyClassicDef

instance (PrettyClassic tyname, Pretty (SomeHead uni), Pretty ann) =>
            Pretty (Type tyname uni ann) where
    pretty = prettyClassicDef

instance
        ( PrettyClassic tyname
        , PrettyClassic name
        , Pretty (SomeHead uni)
        , Pretty (Some uni)
        , Closed uni, uni `Everywhere` PrettyConst
        , Pretty fun
        , Pretty ann
        ) => Pretty (Term tyname name uni fun ann) where
    pretty = prettyClassicDef

instance
        ( PrettyClassic tyname
        , PrettyClassic name
        , Pretty (SomeHead uni)
        , Pretty (Some uni)
        , Closed uni, uni `Everywhere` PrettyConst
        , Pretty fun
        , Pretty ann
        ) => Pretty (Program tyname name uni fun ann) where
    pretty = prettyClassicDef
