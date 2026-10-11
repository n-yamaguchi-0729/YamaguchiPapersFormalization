/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.All
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.All
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.All
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.All
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.All
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.All
import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.All
import ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.All

/-!
# Equal-characteristic Lubin--Tate theory

Public aggregate for the equal-characteristic Lubin--Tate construction.  It
includes the Laurent-series model, finite and completed Lubin--Tate levels,
and the Frobenius and theta constructions.  The local-class-field-theory
norm-subgroup calculation and its transport live in
`LocalClassFieldTheory.LubinTateApplication`.

Each mathematical stage has a reader-facing aggregate below
`LubinTate.EqualCharacteristic`; declarations remain in the matching
namespace.
-/

