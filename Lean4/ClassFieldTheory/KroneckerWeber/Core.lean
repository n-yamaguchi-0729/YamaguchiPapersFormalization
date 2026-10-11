/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
import ClassFieldTheory.KroneckerWeber.RationalCyclotomicArithmeticReciprocity
import ClassFieldTheory.KroneckerWeber.Final
import ClassFieldTheory.KroneckerWeber.GlobalCompositumCyclotomicTarget
import ClassFieldTheory.KroneckerWeber.GlobalCompositumGlobalEmbedding
import ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors
import ClassFieldTheory.KroneckerWeber.GlobalCompositumLocalizationEmbedding
import ClassFieldTheory.KroneckerWeber.GlobalCompositumValuationInertiaBound
import ClassFieldTheory.KroneckerWeber.GlobalCompositumValuedEmbedding
import ClassFieldTheory.KroneckerWeber.GlobalPadicPrimePowInertiaBound
import ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic
import ClassFieldTheory.KroneckerWeber.RayClassComparison
import ClassFieldTheory.KroneckerWeber.Setup
import ClassFieldTheory.KroneckerWeber.UnramifiedCompositumSupport

/-!
# Kronecker--Weber

The reader-facing entry point for the local and global Kronecker--Weber
theorems.  Importing this module exposes both supported endpoints.
-/

/-!
# The global Kronecker--Weber theorem

Every finite abelian extension of `ℚ` is contained in a cyclotomic field.
The arithmetic construction and global degree estimate are kept in the
semantic support modules under `KroneckerWeber.Global`; this root exposes the
canonical theorem statement.
-/

noncomputable section

namespace KroneckerWeber

/-- **Global Kronecker--Weber.**

Every finite abelian extension of `ℚ` embeds in `ℚ(ζₙ)` for some positive
integer `n`.  Here `CyclotomicField n ℚ` is the concrete model of
`ℚ(ζₙ)`. -/
theorem exists_cyclotomicEmbedding
    (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  ⟨kroneckerWeberConductorCandidate (L := L),
    kroneckerWeberConductorCandidate_pos (L := L),
    ⟨kroneckerWeberCyclotomicEmbedding (L := L)⟩⟩

end KroneckerWeber

end
