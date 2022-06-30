{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE TypeApplications #-}
module PlutusLedgerApi.V3.EvaluationContext
    ( EvaluationContext
    , mkEvaluationContext
    , CostModelParams
    , assertWellFormedCostModelParams
    , machineParametersImmediate
    , machineParametersDeferred
    , toMachineParameters
    , CostModelApplyError (..)
    ) where

import PlutusLedgerApi.Common
import PlutusLedgerApi.V3.ParamName as V3

import PlutusCore.Default as Plutus
import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus

import Control.Monad
import Control.Monad.Except

{-|  Build the 'EvaluationContext'.

The input is a list of integer values passed from the ledger and are expected to appear in correct order.
-}
mkEvaluationContext :: MonadError CostModelApplyError m => [Integer] -> m EvaluationContext
mkEvaluationContext = mkDynEvaluationContext Plutus.DefaultFunV2 . toCostModelParams <=< tagWithParamNames @V3.ParamName
