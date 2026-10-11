/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section

/-!
# SmoothProperCurve nontrivial tensor sections of twoChartPoleDatum

Two-chart pole data ensures that the coordinate-ring tensor product with each field fibre is
nontrivial.
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Gluing.Proofs
namespace SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NONEMPTY

theorem exists_mem_fibre_not_mem_range
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (y : Spec (CommRingCat.of R)) :
    ∃ u : C, c.base u = y ∧ u ∉ Set.range ε.1.base := by
  let F := c.fiber y
  let ι := c.fiberι y
  let q := c.fiberToSpecResidueField y
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hsrd : SmoothOfRelativeDimension 1 q :=
    hbc.of_isPullback (IsPullback.of_hasPullback c
      ((Spec (CommRingCat.of R)).fromSpecResidueField y)) inferInstance
  let p : Spec ((Spec (CommRingCat.of R)).residueField y) ⟶ F :=
    pullback.lift ((Spec (CommRingCat.of R)).fromSpecResidueField y ≫ ε.1) (𝟙 _)
      (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])
  have hp : p ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hpι : p ≫ ι = (Spec (CommRingCat.of R)).fromSpecResidueField y ≫ ε.1 :=
    pullback.lift_fst _ _ _
  let x₀ : F := p.base (IsLocalRing.closedPoint ((Spec (CommRingCat.of R)).residueField y))
  have hdvr : IsDiscreteValuationRing (F.presheaf.stalk x₀) :=
    @AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section _ _ F q
      inferInstance hsrd p hp
  let S := F.presheaf.stalk x₀
  let η : Spec (F.presheaf.stalk x₀) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ≠ IsLocalRing.closedPoint S := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field S this.symm
  let u' : F := (F.fromSpecStalk x₀).base η
  have hu' : u' ≠ x₀ := by
    intro h
    apply hη
    apply (F.fromSpecStalk x₀).isEmbedding.injective
    erw [Scheme.fromSpecStalk_closedPoint]
    exact h
  refine ⟨ι.base u', ?_, ?_⟩
  · have : ι.base u' ∈ Set.range (c.fiberι y).base := ⟨u', rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · rintro ⟨y', hy'⟩
    have hcε : ∀ z, c.base (ε.1.base z) = z := fun z => by
      have := Scheme.Hom.comp_apply ε.1 c z
      rw [ε.2] at this
      exact this.symm
    have hyy : y' = y := by
      have h1 := hcε y'
      rw [hy'] at h1
      have : ι.base u' ∈ Set.range (c.fiberι y).base := ⟨u', rfl⟩
      rw [Scheme.Hom.range_fiberι] at this
      rw [← h1]; exact this
    subst hyy
    apply hu'
    apply ι.isEmbedding.injective
    rw [← hy']
    change _ = ι.base (p.base _)
    let cp : Spec ((Spec (CommRingCat.of R)).residueField y') :=
      IsLocalRing.closedPoint ((Spec (CommRingCat.of R)).residueField y')
    have he := congrArg (fun φ : Spec ((Spec (CommRingCat.of R)).residueField y') ⟶ C =>
      φ.base cp) hpι
    have hcp := (Spec (CommRingCat.of R)).fromSpecResidueField_apply y' cp
    exact ((Scheme.Hom.comp_apply p ι cp).symm.trans
      (he.trans ((Scheme.Hom.comp_apply
        ((Spec (CommRingCat.of R)).fromSpecResidueField y') ε.1 cp).trans
          (congrArg ε.1.base hcp)))).symm

end NONEMPTY

namespace NONEMPTY

theorem nontrivial_tensor_fields {R : Type u} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (K F : Type u) [Field K] [Field F] [Algebra R K] [Algebra R F]
    (hK : ∀ r, algebraMap R K r = 0 ↔ r ∈ 𝔭) (hF : ∀ r, algebraMap R F r = 0 ↔ r ∈ 𝔭) :
    Nontrivial (K ⊗[R] F) := by
  let κ := 𝔭.ResidueField
  have liftable : ∀ (L : Type u) [Field L] [Algebra R L], (∀ r, algebraMap R L r = 0 ↔ r ∈ 𝔭) →
      𝔭.primeCompl ≤ (IsUnit.submonoid L).comap (algebraMap R L) := by
    intro L _ _ hL r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero, ne_eq, hL]
    exact hr
  have hK' : 𝔭 ≤ RingHom.ker (algebraMap R K) := fun r hr => (hK r).mpr hr
  have hF' : 𝔭 ≤ RingHom.ker (algebraMap R F) := fun r hr => (hF r).mpr hr
  let algK : Algebra κ K := (Ideal.ResidueField.lift 𝔭 (algebraMap R K) hK'
    (liftable K hK)).toAlgebra
  let algF : Algebra κ F := (Ideal.ResidueField.lift 𝔭 (algebraMap R F) hF'
    (liftable F hF)).toAlgebra
  have : IsScalarTower R κ K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap 𝔭 (algebraMap R K) hK' _ r).symm
  have : IsScalarTower R κ F := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap 𝔭 (algebraMap R F) hF' _ r).symm
  have : Nontrivial (K ⊗[κ] F) := inferInstance
  let L : K ⊗[R] F →ₗ[R] K ⊗[κ] F :=
    TensorProduct.lift
      { toFun := fun k => { toFun := fun f => k ⊗ₜ[κ] f
                            map_add' := fun a b => TensorProduct.tmul_add _ _ _
                            map_smul' := fun r f => by
                              simp only [RingHom.id_apply]
                              rw [← algebraMap_smul κ r f, TensorProduct.tmul_smul,
                                algebraMap_smul] }
        map_add' := fun a b => by ext f; exact TensorProduct.add_tmul _ _ _
        map_smul' := fun r k => by
          ext f
          simp only [RingHom.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
          rw [← algebraMap_smul κ r k, ← algebraMap_smul κ r (k ⊗ₜ[κ] f),
            TensorProduct.smul_tmul'] }
  have hL : L ((1 : K) ⊗ₜ[R] (1 : F)) = (1 : K ⊗[κ] F) := by
    simp [L, TensorProduct.lift.tmul, Algebra.TensorProduct.one_def]
  refine ⟨⟨(1 : K) ⊗ₜ[R] (1 : F), 0, fun h => ?_⟩⟩
  have := congrArg L h
  rw [hL, map_zero] at this
  exact one_ne_zero this

theorem eval_algebraMap_eq_zero_iff
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {U : C.Opens} (u : C) (hu : u ∈ U) (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (C.evaluation U u hu).hom (algebraMap R Γ(C, U) r) = 0 ↔ r ∈ (c.base u).asIdeal := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  erw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, Scheme.basicOpen_appLE,
    basicOpen_eq_of_affine]
  rw [TopologicalSpace.Opens.mem_inf, not_and]
  constructor
  · intro h
    have h2 : u ∉ c ⁻¹ᵁ PrimeSpectrum.basicOpen r := h hu
    change ¬ (c.base u ∈ PrimeSpectrum.basicOpen r) at h2
    exact not_not.mp ((not_congr (PrimeSpectrum.mem_basicOpen r (c.base u))).mp h2)
  · intro hr _
    change ¬ (c.base u ∈ PrimeSpectrum.basicOpen r)
    exact fun h => ((PrimeSpectrum.mem_basicOpen r (c.base u)).mp h) hr

theorem main
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (_hU : IsAffineOpen U) (_hV : IsAffineOpen V) (_hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (_hf : U ⊓ V = C.basicOpen f) (_hg : U ⊓ V = C.basicOpen g)
    (_hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (K : Type u) [Field K] [Algebra R K] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Nontrivial (K ⊗[R] Γ(C, U)) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have : (RingHom.ker (algebraMap R K)).IsPrime := RingHom.ker_isPrime _
  let y : Spec (CommRingCat.of R) := ⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩
  obtain ⟨u, hcu, hur⟩ := exists_mem_fibre_not_mem_range c ε y
  have hu : u ∈ U := (hUε u).mpr hur
  let ev : Γ(C, U) →+* C.residueField u := (C.evaluation U u hu).hom
  let algRF : Algebra R (C.residueField u) := (ev.comp (algebraMap R Γ(C, U))).toAlgebra
  let evₐ : Γ(C, U) →ₐ[R] C.residueField u :=
    { ev with commutes' := fun _ => rfl }
  have hF : ∀ r : R, algebraMap R (C.residueField u) r = 0 ↔ r ∈ RingHom.ker (algebraMap R K) := by
    intro r
    change ev (algebraMap R Γ(C, U) r) = 0 ↔ _
    rw [eval_algebraMap_eq_zero_iff c u hu r, hcu]
  have hK : ∀ r : R, algebraMap R K r = 0 ↔ r ∈ RingHom.ker (algebraMap R K) := fun r => Iff.rfl
  have := nontrivial_tensor_fields (RingHom.ker (algebraMap R K)) K (C.residueField u) hK hF
  exact (Algebra.TensorProduct.map (AlgHom.id K K) evₐ).toRingHom.domain_nontrivial

end NONEMPTY

open scoped TensorProduct in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra in
theorem _root_.AlgebraicGeometry.SmoothProperCurve.nontrivial_tensor_sections_of_twoChartPoleDatum
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (K : Type u) [Field K] [Algebra R K] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Nontrivial (K ⊗[R] Γ(C, U)) :=
  NONEMPTY.main R c ε U V hU hV hUV hUε f g hf hg hfg K
end SmoothProperCurve_nontrivial_tensor_sections_of_twoChartPoleDatum
end AlgebraicCurves.Models.Gluing.Proofs
end ProofImplementation
