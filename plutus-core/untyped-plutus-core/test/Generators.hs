-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

-- | UPLC property tests (pretty-printing\/parsing and binary encoding\/decoding).
module Generators where

import PlutusPrelude (display, fold, on, void)

import PlutusCore (Name, _nameText)
import PlutusCore.Compiler.Erase (eraseProgram)
import PlutusCore.Default (Closed, DefaultFun, DefaultUni, Everywhere, GEq)
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Generators.Hedgehog (forAllPretty)
import PlutusCore.Generators.Hedgehog.AST (AstGen, runAstGen)
import PlutusCore.Generators.Hedgehog.AST qualified as AST
import PlutusCore.Parser (defaultUni, parseGen)
import PlutusCore.Pretty (displayPlcDef)
import PlutusCore.Quote (QuoteT, runQuoteT)
import UntypedPlutusCore.Core.Type (Program (Program),
                                    Term (Apply, Builtin, Constant, Delay, Error, Force, LamAbs, Var))
import UntypedPlutusCore.Parser (SourcePos, parseProgram, parseTerm)

import Data.Text (Text)
import Data.Text qualified as T

import Hedgehog (property, tripping)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Test.Tasty.HUnit (testCase, (@?=))

import Flat qualified

-- | A 'Program' which we compare using textual equality of names rather than alpha-equivalence.
newtype TextualProgram a = TextualProgram
    { unTextualProgram :: Program Name DefaultUni DefaultFun a
    } deriving stock Show

instance Eq a => Eq (TextualProgram a) where
    (TextualProgram p1) == (TextualProgram p2) = compareProgram p1 p2

compareName :: Name -> Name -> Bool
compareName = (==) `on` _nameText

compareTerm
    :: (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq a)
    => Term Name uni fun a -> Term Name uni fun a -> Bool
compareTerm (Var _ n) (Var _ n')              = compareName n n'
compareTerm (LamAbs _ n t) (LamAbs _ n' t')   = compareName n n' && compareTerm t t'
compareTerm (Apply _ t t'') (Apply _ t' t''') = compareTerm t t' && compareTerm t'' t'''
compareTerm (Force _ t ) (Force _ t')         = compareTerm t t'
compareTerm (Delay _ t ) (Delay _ t')         = compareTerm t t'
compareTerm (Constant _ x) (Constant _ y)     = x == y
compareTerm (Builtin _ bi) (Builtin _ bi')    = bi == bi'
compareTerm (Error _ ) (Error _ )             = True
compareTerm _ _                               = False

compareProgram
    :: (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq a)
    => Program Name uni fun a -> Program Name uni fun a -> Bool
compareProgram (Program _ v t) (Program _ v' t') = v == v' && compareTerm t t'

genProgram :: forall fun. (Bounded fun, Enum fun) => AstGen (Program Name DefaultUni fun ())
genProgram = fmap eraseProgram AST.genProgram

propFlat :: TestTree
propFlat = testPropertyNamed "Flat" "Flat" $ property $ do
    prog <- forAllPretty $ runAstGen (Generators.genProgram @DefaultFun)
    tripping prog Flat.flat Flat.unflat

propParser :: TestTree
propParser = testPropertyNamed "Parser" "parser" $ property $ do
    prog <- TextualProgram <$> forAllPretty (runAstGen Generators.genProgram)
    tripping prog (displayPlcDef . unTextualProgram)
                (\p -> fmap (TextualProgram . void) (parseProg p))
    where
        parseProg
            :: T.Text -> Either ParserErrorBundle (Program Name DefaultUni DefaultFun SourcePos)
        parseProg = runQuoteT . parseProgram

propUnit :: TestTree
propUnit = testCase "Unit" $ fold
    [ pTerm "(con bool True)"
        @?= "(con bool True)"
    , pTerm "(con (list bool) [True, False])"
        @?= "(con (list bool) [True,False])"
    , pTerm "(con (pair unit (list integer)) ((),[1,2,3]))"
        @?= "(con (pair unit (list integer)) ((), [1,2,3]))"
    , pTerm "(con (list (pair string bool)) [(\"abc\", True), (\"def\", False)])"
        @?= "(con (list (pair string bool)) [(\"abc\", True), (\"def\", False)])"
    , pTerm "(con string \"abc\")"
        @?= "(con string \"abc\")"
    ]
    where
        pTerm :: String -> Text
        pTerm
            = either (error . display) display
            . runQuoteT
            . parseTerm @_ @(QuoteT (Either ParserErrorBundle))
            . T.pack

propDefaultUni :: TestTree
propDefaultUni = testCase "DefaultUni" $ fold
    [ pDefaultUni "bool" @?= "bool"
    , pDefaultUni "list" @?= "list"
    , pDefaultUni "(list integer)" @?= "(list integer)"
    , pDefaultUni "(pair (list bool))" @?= "(pair (list bool))"
    , pDefaultUni "(pair (list unit) integer)" @?= "(pair (list unit) integer)"
    , pDefaultUni "(list (pair unit integer))" @?= "(list (pair unit integer))"
    , pDefaultUni "(pair unit (pair bool integer))" @?= "(pair unit (pair bool integer))"
    ]
    where
        pDefaultUni :: String -> Text
        pDefaultUni
            = either (error . display) display
            . runQuoteT
            . parseGen @_ @(QuoteT (Either ParserErrorBundle)) defaultUni
            . T.pack

test_parsing :: TestTree
test_parsing = testGroup "Parsing"
               [ propFlat
               , propParser
               , propUnit
               , propDefaultUni
               ]
