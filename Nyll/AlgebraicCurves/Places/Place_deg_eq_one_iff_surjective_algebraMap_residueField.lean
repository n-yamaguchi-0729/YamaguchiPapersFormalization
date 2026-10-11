/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.LaurentBaseChange

/-!
# Place deg eq one iff surjective algebra Map residue Field
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.PlaceDegOneIffSurjectiveAlgebra

open _root_.AlgebraicCurve
open _root_.ModularCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
private theorem AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField_aux
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) := by
  unfold Place.deg
  rw [show Function.Surjective (algebraMap K v.ResidueField)
        ↔ Function.Bijective (algebraMap K v.ResidueField) from
      ⟨fun h => ⟨(algebraMap K v.ResidueField).injective, h⟩, fun h => h.2⟩]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Places.Proofs.PlaceDegOneIffSurjectiveAlgebra.AlgebraicCurve ModularCurve
  in
theorem _root_.AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField {K F :
  Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) :=
  AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField_aux v

end AlgebraicCurves.Places.Proofs.PlaceDegOneIffSurjectiveAlgebra
end ProofImplementation
