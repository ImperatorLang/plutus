module Plugin.Spec where

import Plugin.Basic.Spec
import Plugin.Coverage.Spec
import Plugin.Data.Spec
import Plugin.Errors.Spec
import Plugin.Functions.Spec
import Plugin.Laziness.Spec
import Plugin.NoTrace.Spec
import Plugin.Primitives.Spec
import Plugin.Profiling.Spec
import Plugin.Strict.Spec
import Plugin.Typeclasses.Spec
import Test.Tasty.Extras

tests :: TestNested
tests = testNested "Plugin" [
    basic
  , primitives
  , datat
  , functions
  , laziness
  , noTrace
  , errors
  , typeclasses
  , strict
  , profiling
  , coverage
  ]
