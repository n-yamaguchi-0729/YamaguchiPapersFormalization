/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FunctionFields.Functoriality
import SchemeTheory.FunctionFields.GeometricIntegrality
import SchemeTheory.FunctionFields.IntegerBase
import SchemeTheory.FunctionFields.ArithmeticGeometricIntegrality
import SchemeTheory.FunctionFields.PlainIntegerBase
import SchemeTheory.FunctionFields.PrimeDivisors.All
import SchemeTheory.FunctionFields.SeparableClosure.All
import SchemeTheory.FunctionFields.StalkFactorization
import SchemeTheory.FunctionFields.Transcendence
import SchemeTheory.FunctionFields.Valuations.All
import SchemeTheory.FunctionFields.StalkFunctoriality

/-!
# Function fields and prime divisors

This facade collects functoriality for dominant morphisms, function-field
transcendence, valuation-theoretic prime divisors and their counting theorems,
together with ring covers of domains.
-/

/- Canonical aggregate for SchemeTheory.FunctionFields. -/
