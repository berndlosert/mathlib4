/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean.Meta.Tactic.Simp.Types

import Std.Lean.HashSet

import Mathlib.Logic.Function.Basic

/-!
## `fprop`

this file defines enviroment extension for `fprop`
-/


namespace Mathlib
open Lean Meta

namespace Meta.FProp


initialize registerTraceClass `Meta.Tactic.fprop.attr
initialize registerTraceClass `Meta.Tactic.fprop
initialize registerTraceClass `Meta.Tactic.fprop.step
initialize registerTraceClass `Meta.Tactic.fprop.unify
initialize registerTraceClass `Meta.Tactic.fprop.discharge
initialize registerTraceClass `Meta.Tactic.fprop.apply
initialize registerTraceClass `Meta.Tactic.fprop.unfold
initialize registerTraceClass `Meta.Tactic.fprop.cache


/-- -/
structure Config where
  /-- Name to unfold -/
  constToUnfold : HashSet Name := .ofArray #[``id, ``Function.comp, ``Function.HasUncurry.uncurry]
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr → MetaM (Option Expr) := fun _ => pure .none
  /-- Maximal number of transitions between function properties
  e.g. infering differentiability from linearity -/
  maxTransitionDepth := 20
  /-- Stack of used theorem, used to prevent trivial loops. -/
  thmStack    : List Origin := []

/-- -/
structure State where
  /-- Simp's cache is used as the `fprop` tactic is designed to be used inside of simp and utilize
  its cache -/
  cache        : Simp.Cache := {}
  /-- The number of used transition theorems. -/
  transitionDepth := 0

/-- Log used theorem -/
def Config.addThm (cfg : Config) (thmId : Origin) :
    Config :=
  {cfg with thmStack := thmId :: cfg.thmStack}

/-- -/
abbrev FPropM := ReaderT FProp.Config $ StateT FProp.State MetaM


/-- Result of `fprop`, it is a proof of function property `P f` -/
structure Result where
  /-- -/
  proof : Expr

/-- Get the name of previously used theorem. -/
def getLastUsedTheoremName : FPropM (Option Name) := do
  match (← read).thmStack.head? with
  | .some (.decl n) => return n
  | _ => return none
