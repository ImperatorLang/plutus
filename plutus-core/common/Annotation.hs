module Annotation where

import Data.Semigroup (Any (..))
import GHC.Generics
import Prettyprinter
import Data.Set (Set)

newtype InlineHints name a = InlineHints { shouldInline :: a -> name -> Bool }
    deriving (Semigroup, Monoid) via (a -> name -> Any)

instance Show (InlineHints name a) where
    show _ = "<inline hints>"

-- | An annotation type used during the compilation.
data Ann = Ann
    { annInline   :: Inline
    , annSrcSpans :: SrcSpans
    }
    deriving stock (Eq, Ord, Generic, Show)

data Inline
    = -- | When calling @PlutusIR.Compiler.Definitions.defineTerm@ to add a new term definition,
      -- if we annotation the var on the LHS of the definition with `AlwaysInline`, the inliner will
      -- always inline that var.
      --
      -- This is currently used to ensure builtin functions such as @trace@ (when the @remove-trace@
      -- flag is on and @trace@ is rewritten to @const@) are inlined, because the inliner would
      -- otherwise not inline them. To achieve that, we annotate the definition with `AlwaysInline`
      -- when defining @trace@, i.e., @trace <AlwaysInline> = \_ a -> a@.
      AlwaysInline
    | MayInline
    deriving stock (Eq, Ord, Generic, Show)

instance Pretty Ann where
    pretty = viaShow

-- | Create an `Ann` with `AlwaysInline`.
annAlwaysInline :: Ann
annAlwaysInline = Ann{annInline = AlwaysInline, annSrcSpans = mempty}

-- | Create an `Ann` with `MayInline`.
annMayInline :: Ann
annMayInline = Ann{annInline = MayInline, annSrcSpans = mempty}

-- | The span between two source locations.
--
-- This corresponds roughly to the `SrcSpan` used by GHC, but we define our own version so we don't have to depend on `ghc` to use it.
--
-- The line and column numbers are 1-based, and the unit is Unicode code point (or `Char`).
data SrcSpan = SrcSpan
    { srcSpanFile  :: FilePath
    , srcSpanSLine :: Int
    , srcSpanSCol  :: Int
    , srcSpanELine :: Int
    , srcSpanECol  :: Int
    }
    deriving stock (Eq, Ord, Generic, Show, Read)

instance Pretty SrcSpan where
    pretty = viaShow

type SrcSpans = Set SrcSpan

