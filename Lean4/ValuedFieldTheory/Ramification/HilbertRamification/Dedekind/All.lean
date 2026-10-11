/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Conjugation
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFieldTower
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFieldUnramified
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.OrbitCardinality
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.PrimeContractions
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.TowerInvariants
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.ValuedGalois

/-!
# Hilbert ramification over Dedekind domains

This aggregate exposes prime contractions, decomposition and fixed fields, conjugation,
orbit cardinalities, and valued Galois comparisons in Dedekind extensions.
-/
