/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Ideal

/-!
# maximal Ideal stalk eq span stalk Specializes of ker stalk Map eq span
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Topology

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

namespace Scheme
open _root_.AlgebraicGeometry.Scheme
end Scheme
open scoped _root_.AlgebraicGeometry.Scheme in
private theorem Scheme.map_comap_stalkSpecializes {X : Scheme.{u}} {x y : X} (h : y ⤳ x)
    (J : Ideal (X.presheaf.stalk y)) :
    (J.comap (X.presheaf.stalkSpecializes h).hom).map (X.presheaf.stalkSpecializes h).hom = J := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  let iAx : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  let iAy : Algebra Γ(X, U) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
  have hlx := hU.isLocalization_stalk ⟨x, hxU⟩
  have hly := hU.isLocalization_stalk ⟨y, hyU⟩
  let iA : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (X.presheaf.stalk y) := by
    apply IsScalarTower.of_algebraMap_eq'
    simp_rw [RingHom.algebraMap_toAlgebra]
    change (X.presheaf.germ U y hyU).hom = (X.presheaf.germ U x hxU ≫ X.presheaf.stalkSpecializes
      h).hom
    rw [X.presheaf.germ_stalkSpecializes]
  have hsp : (⟨y, hyU⟩ : U) ⤳ (⟨x, hxU⟩ : U) :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp h
  have hle : hU.primeIdealOf ⟨y, hyU⟩ ≤ hU.primeIdealOf ⟨x, hxU⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (hsp.map hU.isoSpec.hom.continuous)
  have hle' : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ≤
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl := by
    intro a ha hay
    exact ha ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hle hay)
  have := IsLocalization.isLocalization_of_submonoid_le (X.presheaf.stalk x) (X.presheaf.stalk y)
    _ _ hle'
  exact IsLocalization.map_under (M := ((hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl.map
    (algebraMap Γ(X, U) (X.presheaf.stalk x)))) (S := X.presheaf.stalk y) J

private theorem Scheme.functionField_algebraMap_injective (Y : Scheme.{u}) [IsIntegral Y]
    (y : Y) : Function.Injective (algebraMap (Y.presheaf.stalk y) Y.functionField) :=
  IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField

open scoped _root_.AlgebraicGeometry.Scheme in
private theorem Scheme.stalkSpecializes_genericPoint_closedPoint_injective
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] :
    Function.Injective ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
      (genericPoint_specializes (IsLocalRing.closedPoint A))).hom :=
  Scheme.functionField_algebraMap_injective (Spec (CommRingCat.of A)) (IsLocalRing.closedPoint A)

end AlgebraicGeometry

open maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span.AlgebraicGeometry.Scheme in
theorem _root_.AlgebraicGeometry.maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec
      (CommRingCat.of A))
    (σ : Spec (CommRingCat.of A) ⟶ X) (_hσ : σ ≫ c = 𝟙 _)
    (t : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A)))
    (ht : RingHom.ker (σ.stalkMap (IsLocalRing.closedPoint A)).hom = Ideal.span {t}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk (σ.base (genericPoint ↥(Spec (CommRingCat.of A))))) =
      Ideal.span {(X.presheaf.stalkSpecializes
        (((genericPoint_specializes (IsLocalRing.closedPoint A)).map σ.continuous) :
          σ.base (genericPoint ↥(Spec (CommRingCat.of A))) ⤳ σ.base (IsLocalRing.closedPoint
            A))).hom t} := by
  clear _hσ
  set hs := genericPoint_specializes (α := ↥(Spec (CommRingCat.of A))) (IsLocalRing.closedPoint A)
    with hs_def
  set h : σ.base (genericPoint ↥(Spec (CommRingCat.of A))) ⤳ σ.base (IsLocalRing.closedPoint A) :=
    hs.map σ.continuous with h_def
  rw [← map_comap_stalkSpecializes h (IsLocalRing.maximalIdeal _)]
  suffices hc : (IsLocalRing.maximalIdeal _).comap (X.presheaf.stalkSpecializes h).hom =
      Ideal.span {t} by
    rw [hc, Ideal.map_span, Set.image_singleton]
    rfl
  rw [← ht]
  ext a
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [← IsLocalRing.maximalIdeal_comap
    (σ.stalkMap (genericPoint ↥(Spec (CommRingCat.of A)))).hom, Ideal.mem_comap]
  have hnat := Scheme.Hom.stalkSpecializes_stalkMap_apply σ
    (genericPoint ↥(Spec (CommRingCat.of A))) (IsLocalRing.closedPoint A) hs a
  erw [hnat]
  have hF : IsLocalRing.maximalIdeal
      ((Spec (CommRingCat.of A)).presheaf.stalk (genericPoint ↥(Spec (CommRingCat.of A)))) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField _)
  rw [hF, Ideal.mem_bot]
  exact map_eq_zero_iff _ (stalkSpecializes_genericPoint_closedPoint_injective A)
end maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
