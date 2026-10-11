/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_Differentials.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Basic
-/

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

open Classical in
/-- A chosen element of order one at the place, or zero if no such element exists. -/
def uniformizer_alt : F :=
  if h : ∃ t : F, v.ord t = 1 then h.choose else 0

theorem ord_uniformizer_alt (h : ∃ t : F, v.ord t = 1) : v.ord v.uniformizer_alt = 1 := by
  rw [uniformizer_alt, dite_eq_left h]
  exact h.choose_spec

open Classical in
/-- A chosen coefficient expressing the differential as a multiple of `D t`, or zero if none
exists. -/
def diffCoeff (t : F) (ω : Ω[F⁄K]) : F :=
  if h : ∃ g : F, ω = g • D K F t then h.choose else 0

theorem diffCoeff_smul_D {t : F} {ω : Ω[F⁄K]} (h : ∃ g : F, ω = g • D K F t) :
    diffCoeff t ω • D K F t = ω := by
  rw [diffCoeff, dite_eq_left h]
  exact h.choose_spec.symm

theorem diffCoeff_of_not_exists {t : F} {ω : Ω[F⁄K]} (h : ¬ ∃ g : F, ω = g • D K F t) :
    diffCoeff t ω = 0 := by
  rw [diffCoeff, dite_eq_right h]

/-- The order of the differential coefficient with respect to the chosen uniformizer. -/
def ordDiff (ω : Ω[F⁄K]) : ℤ :=
  v.ord (diffCoeff v.uniformizer_alt ω)

theorem ordDiff_def (ω : Ω[F⁄K]) : v.ordDiff ω = v.ord (diffCoeff v.uniformizer_alt ω) := rfl

end Place

variable (K F) in
/-- A differential is regular when its order is nonnegative at every place. -/
def IsRegularDiff (ω : Ω[F⁄K]) : Prop :=
  ∀ v : Place K F, 0 ≤ v.ordDiff ω

theorem isRegularDiff_iff (ω : Ω[F⁄K]) :
    IsRegularDiff K F ω ↔ ∀ v : Place K F, 0 ≤ v.ordDiff ω := Iff.rfl

variable (K F) in
/-- The submodule spanned by the differentials that are regular at every place. -/
def regularDiffs : Submodule K Ω[F⁄K] :=
  Submodule.span K {ω : Ω[F⁄K] | IsRegularDiff K F ω}

theorem mem_regularDiffs_of_isRegularDiff {ω : Ω[F⁄K]} (h : IsRegularDiff K F ω) :
    ω ∈ regularDiffs K F :=
  Submodule.subset_span h

theorem regularDiffs_eq_span :
    regularDiffs K F = Submodule.span K {ω : Ω[F⁄K] | IsRegularDiff K F ω} := rfl

section Pullback

variable {F' : Type*} [Field F'] [Algebra K F']

/-- The map on Kähler differentials induced by the given homomorphism of function fields. -/
def pullbackDiff (φ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F'⁄K] :=
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  (KaehlerDifferential.map K K F F').restrictScalars K

theorem pullbackDiff_D (φ : F →ₐ[K] F') (x : F) :
    pullbackDiff φ (D K F x) = D K F' (φ x) := by
  let : Algebra F F' := φ.toRingHom.toAlgebra
  have : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  exact KaehlerDifferential.map_D K K F F' x

end Pullback

end AlgebraicCurve

end
