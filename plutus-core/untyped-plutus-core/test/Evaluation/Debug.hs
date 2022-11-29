{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
module Evaluation.Debug
    ( test_debug
    ) where

import Annotation
import PlutusCore (Everywhere, GShow)
import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Driver
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal

import Test.Tasty
import Test.Tasty.Golden
import Data.ByteString.Lazy.Char8 qualified as BS
import Control.Monad.ST (RealWorld)
import Data.Ix
import Control.Monad.RWS

test_debug :: TestTree
test_debug =
    let ?cekRuntime = undefined
        ?cekEmitter = undefined
        ?cekBudgetSpender = undefined
        ?cekCosts = undefined
        ?cekSlippage = defaultSlippage
    in
    testGroup "debug" $
        fmap goldenVsDebug examples

examples :: [(String, [Cmd], DTerm DefaultUni DefaultFun)]
examples = [ ("ex1", [], Error [])
           , ("ex2", [], Error [])
           ]

goldenVsDebug (name, cmds, term) =
    goldenVsString name
    ("untyped-plutus-core/test/Evaluation/Debug/" ++ name ++ ".golden")
    (BS.pack . unlines <$> mock cmds term)

-- A Mocking interpreter

type Mocking uni fun t m = ( Ix fun, PrettyUni uni fun, GivenCekReqs uni fun SrcSpans RealWorld
                           , MonadTrans t
                           -- | the mock client feeds commands
                           , MonadReader [Cmd] (t m)
                           -- | and logs to some string output
                           , MonadWriter [String] (t m)
                           )

mock :: ( Ix fun, PrettyUni uni fun, GivenCekReqs uni fun SrcSpans RealWorld
       , uni `Everywhere` Show, GShow uni, Show fun
       )
     => [Cmd] -- ^ commands to feed
     -> DTerm uni fun -- ^ term to debug
     -> IO [String] -- ^ mocking output
mock cmds = cekMToIO . runMocking . mockerInterprets . runDriver
    where
      -- TODO: use cutoff or partialIterT to prevent runaway
      mockerInterprets = iterTM handle
      runMocking m = fmap snd $ execRWST m cmds ()

-- Interpretation of the mocker
-------------------------------

handle :: ( Mocking uni fun t m
         , m ~ CekM uni fun RealWorld
         )
       => DebugF uni fun (t m ()) -> t m ()
handle = \case
    StepF prevState k -> lift (handleStep prevState) >>= k
    InputF k     -> handleInput k
    LogF text k  -> handleLog text >> k
    UpdateClientF _ k -> k -- ignore
  where

    -- more general as :: (MonadReader [Cmd] m, MonadWriter [String] m) => (Cmd -> m ()) -> m ()
    handleInput :: Mocking uni fun t m => (Cmd -> t m ()) -> t m ()
    handleInput k = do
        cmds <- ask
        case cmds of
            [] ->
                tell ["Early run out of commands"]
            (cmd:cmds') ->
                local (const cmds') $
                    -- continue by feeding the next command to continuation
                    k cmd

    -- more general as handleLog :: (MonadWriter [String] m) => String -> m ()
    handleLog :: Mocking uni fun t m => String -> t m ()
    handleLog = tell . pure
