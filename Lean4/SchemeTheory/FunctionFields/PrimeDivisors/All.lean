/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FunctionFields.PrimeDivisors.Basic
import SchemeTheory.FunctionFields.PrimeDivisors.Centered
import SchemeTheory.FunctionFields.PrimeDivisors.CenteredTransport
import SchemeTheory.FunctionFields.PrimeDivisors.Counting
import SchemeTheory.FunctionFields.PrimeDivisors.Dedekind
import SchemeTheory.FunctionFields.PrimeDivisors.DegreeOne
import SchemeTheory.FunctionFields.PrimeDivisors.Infinity
import SchemeTheory.FunctionFields.PrimeDivisors.InseparableCounting
import SchemeTheory.FunctionFields.PrimeDivisors.IntegralClosure
import SchemeTheory.FunctionFields.PrimeDivisors.PrimesOver
import SchemeTheory.FunctionFields.PrimeDivisors.Transport

/-!
# Prime divisors of function fields

This aggregate exposes centered prime divisors, degree and counting comparisons,
integral-closure primes, divisors at infinity, and transport across function-field maps.
-/

/- Canonical aggregate for SchemeTheory.FunctionFields.PrimeDivisors. -/
