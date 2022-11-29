{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Driver
    ( Breakpoint (..)
    , Breakpoints
    , DriverState
    , Cmd (..)
    , DTerm
    , runDriver
    , DebugF (..)
    -- | Reexport some functions for convenience
    , handleStep
    , F.MonadFree
    , F.iterM
    , F.iterTM
    , F.partialIterT
    , F.cutoff
    ) where

import Annotation
import UntypedPlutusCore
import UntypedPlutusCore.Evaluation.Machine.Cek.Debug.Internal

import Data.RandomAccessList.Class qualified as Env
import Data.Word64Array.Word8 hiding (Index, toList)
import Control.Monad.Reader
import Control.Monad.Trans.Free as F
import Control.Lens hiding (Context)
import Prettyprinter
import Data.Set
import Data.Function

{- Note [Stepping the driver]

The client instructs the driver to do a single step of the Cek (`Step` Cmd) or multiple steps until a condition is met
(`Continue`,`Next`,`Finish`). The driver upon receiving a Command (via `inputF`) fires a series
of `stepF` actions to fulfill the command. A `stepF` action is supposed to move the underlying CEK machine a *single* step forward.
Since the driver is written as a free monad, the interpretation of the `stepF` action is left open.

When the driver calls `stepF  state`, it yields its coroutine with the current driver/cek state (before the stepping interpretation).
The interpreter of `stepF` receives the currentState and calculates a newstate from it (e.g. **actually stepping the cek machine**).
The interpreter then resumes the driver coroutine with the new state.

The sensible interpretation to this is the CEK's state transition function (`handleStep oldState ===> newState`),
but other exotic options may be: logging the before/after states, or even "mutating" the running program's variables
in the environment before/after the state transition (similar to C debuggers).
The interpreter can even supply a different state transition function (e.g. `id`), but we see little benefit in it at the moment.
Currently all interpreters (brick,repl,testing) just call`handleStep`.
-}


-- | Usually a breakpoint is only a line number, but it does not hurt to be more general as a srcspan
newtype Breakpoint = Breakpoint { unBreakpoint :: SrcSpan }
    deriving newtype (Show, Pretty, Read, Eq, Ord)

-- | Treat them as `Set`s like `SrcSpan`
type Breakpoints = Set Breakpoint

-- | The `Term`s that makes sense to debug
type DTerm uni fun = Term NamedDeBruijn uni fun SrcSpans

-- | The commands that the driver may receive from the client (tui,cli,test,etc)
data Cmd
  = Step -- ^ Instruct the driver to a *SINGLE* step.
         -- Note: No need to pass breakpoints here because the stepping granularity is minimal.
  | Continue Breakpoints -- ^ Instruct to multi-step until end-of-program or until breakpoint reached
  | Next Breakpoints -- ^ Instruct to multi-step over the function call at point (a.k.a. Next) or until breakpoint reached
  | Finish Breakpoints -- ^ Instruct to multi-step to the end of current function or until breakpoint reached
  deriving stock (Show, Read)

-- | The driver's state is the cek's state but fixed to SrcSpans annotations
type DriverState uni fun = CekState uni fun SrcSpans

-- | The drivers's suspension functor
data DebugF uni fun a
   -- | Await for the client (e.g. TUI) to tell what to do next (Cmd).
  = InputF (Cmd -> a)
    -- | A generator of logging messages of the driver
  | LogF String a
    -- | An enumeratee of Driver State (generator+iteratee):
    -- Yield a state before doing a step, then await for a state to resume after the step. See Note [Stepping the driver].
  | StepF
      (DriverState uni fun) -- ^ yield with the current driver's state before running a step
      (DriverState uni fun -> a) -- ^ resume back with a state after the step interpretation
    -- | A generator of DriverState to yield to client (e.g. TUI)
  | UpdateClientF (DriverState uni fun) a
  deriving stock Functor

-- | The monad that the driver operates in
type Driving m uni fun =
    ( MonadReader (DriverState uni fun) m -- ^ the state of the debugger
    , MonadFree (DebugF uni fun) m -- ^ the effects of the driver
    )

-- | Entrypoint of the driver
runDriver :: MonadFree (DebugF uni fun) m
          => DTerm uni fun -> m ()
runDriver = void . runReaderT driver . initState
    where
      initState :: DTerm uni fun -> DriverState uni fun
      initState = Computing (toWordArray 0) NoFrame Env.empty

-- | The driver action. The driver repeatedly:
---
-- 1) waits for a `Cmd`
-- 2) runs one or more CEK steps
-- 3) informs the client for CEK updates&logs
---
-- The driver computation exits when it reaches a CEK `Terminating` state.
driver :: Driving m uni fun => m ()
driver = inputF >>= \case
    -- Condition immediately satisfied
    Step -> multiStepUntil $ const True

    Continue bs -> multiStepUntil $ atBreakpoint bs

    Next bs -> do
        startState <- ask
        multiStepUntil $ \curState ->
            atBreakpoint bs curState ||
            -- has activation record length been restored?
            let leCtx = onCtxLen (<)
            in curState `leCtx` startState

    Finish bs -> do
        startState <- ask
        multiStepUntil $ \curState ->
            atBreakpoint bs curState ||
            -- has activation record length become smaller?
            let ltCtx = onCtxLen (<=)
            in curState `ltCtx` startState
  where
    -- | Comparison on states' contexts
    onCtxLen :: (state ~ CekState uni fun ann
               , ctxLen ~ Maybe Word -- `Maybe` because ctx can be missing if terminating
               )
             => (ctxLen -> ctxLen -> a)
             -> state -> state -> a
    onCtxLen = (`on` preview (cekStateContext . to lenContext))

-- | Do one or more cek steps until a condition on the 'DriverState' is met
multiStepUntil :: Driving m uni fun
               => (DriverState uni fun -> Bool) -> m ()
multiStepUntil cond = do
    logF "About to do a single step"
    newState <- stepF =<< ask
    case newState of
        Terminating{} ->
            -- don't recurse to driver, but EXIT the driver
            updateClientF newState
        _ -> -- update state
            local (const newState) $
                if cond newState
                then do
                    updateClientF newState
                    driver -- tail recurse
                else
                    multiStepUntil cond -- tail recurse

-- | Given the debugger's state, have we reached a breakpoint?
atBreakpoint :: Breakpoints -> DriverState uni fun -> Bool
atBreakpoint _bs = \case
    -- FIXME: stub, implement this, could we use PlutusLedgerAPI.V1.Interval api for it?
    Computing{} -> False
    _ -> False

-- * boilerplate "suspension actions"
-- Being in 'Driving' monad here is too constraining, but it does not matter.
inputF :: Driving m uni fun => m Cmd
inputF = liftF $ InputF id
logF :: Driving m uni fun => String -> m ()
logF text = liftF $ LogF text ()
updateClientF :: Driving m uni fun => DriverState uni fun -> m ()
updateClientF dState = liftF $ UpdateClientF dState ()
stepF :: Driving m uni fun => DriverState uni fun -> m (DriverState uni fun)
stepF yieldState = liftF $ StepF yieldState id
