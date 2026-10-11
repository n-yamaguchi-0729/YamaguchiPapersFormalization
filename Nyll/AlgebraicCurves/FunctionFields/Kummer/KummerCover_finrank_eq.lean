/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Mathlib.FieldTheory.KummerExtension

/-!
# Kummer Cover finrank eq
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Kummer.Proofs.KummerCover_finrank_eq

open Polynomial IntermediateField
namespace AlgebraicCurve
namespace KummerCover
section Pure
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {p : ℕ} [hp : Fact p.Prime] {f : F} {α : L}
private theorem irreducible_X_pow_sub_C (hf : ∀ g : F, g ^ p ≠ f) : Irreducible (X ^ p - C f) :=
  X_pow_sub_C_irreducible_of_prime hp.out hf
end Pure
end AlgebraicCurve.KummerCover

open Polynomial AlgebraicCurve.KummerCover in
theorem _root_.AlgebraicCurve.KummerCover.finrank_eq {F L : Type*} [Field F] [Field L] [Algebra F
  L] {p : ℕ} [hp : Fact p.Prime] {f : F}
    [IsSplittingField F L (X ^ p - C f)] (hζ : (primitiveRoots p F).Nonempty) (hf : ∀ g : F, g ^ p
      ≠ f) :
    Module.finrank F L = p :=
  finrank_of_isSplittingField_X_pow_sub_C hζ (irreducible_X_pow_sub_C hf) L

end AlgebraicCurves.FunctionFields.Kummer.Proofs.KummerCover_finrank_eq
end ProofImplementation
