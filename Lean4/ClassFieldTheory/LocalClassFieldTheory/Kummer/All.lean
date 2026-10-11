/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LocalClassFieldTheory.Kummer.CanonicalKummerNorm
import ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerExponentTower
import ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerNormPowerClassDegree
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertExponentCompatibility
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairingNondegeneracy
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbolLaws
import ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
import ClassFieldTheory.LocalClassFieldTheory.Kummer.MaximalLocalKummerPairing
import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
import ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport

/-!
# Local Kummer reciprocity

Aggregate for the local Hilbert symbol, its laws, and the maximal local Kummer
pairing, including the tame power-residue formula.
-/

