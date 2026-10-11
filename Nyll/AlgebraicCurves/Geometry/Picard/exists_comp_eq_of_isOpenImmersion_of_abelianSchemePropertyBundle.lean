/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality

/-!
# exists comp eq of is Open Immersion of abelian Scheme Property Bundle
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
attribute [-instance] instTopologicallyFGOfFiniteType

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


universe u

noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (IsLocallyNoetherian Scheme.PartialMap.compHom_hom
  Scheme.PartialMap.toPartialMap_toRationalMap_restrict Scheme.PartialMap IsProper
  LocallyOfFiniteType.isLocallyNoetherian Scheme.PartialMap.restrict_hom
  Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated UniversallyClosed QuasiCompact
  LocallyOfFiniteType Spec IsIntegral Scheme Smooth Scheme.PartialMap.isOver_iff
  isReduced_of_isReduced_stalk Scheme.RationalMap IsOpenImmersion
  isIntegral_iff_irreducibleSpace_and_isReduced UniversallyClosed.eq_valuativeCriterion
  Scheme.RationalMap.toRationalMap_toPartialMap IsReduced IsSeparated Scheme.homOfLE_ι
  ValuativeCriterion.Existence ValuativeCriterion Scheme.ΓSpecIso
  Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
  Smooth.isDomain_and_isIntegrallyClosed_stalk)

namespace WeilExtField
namespace EXT

open _root_.AlgebraicGeometry


scoped instance isDomain_sections_spec (k : Type u) [Field k] :
    IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
  MulEquiv.isDomain k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

scoped instance isIntegrallyClosed_sections_spec (k : Type u) [Field k] :
    IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
  IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm

theorem isReduced_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of k)) [Smooth g] : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk g x).1
    infer_instance
  exact isReduced_of_isReduced_stalk _

theorem valuationRing_stalk_of_ringKrullDim_le_one (k : Type u) [Field k] {X : Scheme.{u}}
  [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of k)) [Smooth g] (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) ≤ 1) : ValuationRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨-, hic⟩ := AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk g x
  have : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr hx
  have key := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 4 2
  exact key.mp ⟨hic, fun P hP hP' => IsLocalRing.eq_maximalIdeal (hP'.isMaximal_of_ne_bot hP)⟩

open _root_.GoodReductionJacobian.RelativeGroupLaw in
theorem main
    {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [IsSeparated g] [QuasiCompact g] [IrreducibleSpace X]
    {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k fA)
    {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u] [Nonempty U]
    (φ : U ⟶ A) (hφ : φ ≫ fA = u ≫ g) :
    ∃ ψ : X ⟶ A, ψ ≫ fA = g ∧ u ≫ ψ = φ := by
  classical
  obtain ⟨L⟩ := hA.hasGroupLaw
  have : IsProper fA := hA.proper
  have : IsReduced X := isReduced_of_smooth k g
  have : IsIntegral X := (isIntegral_iff_irreducibleSpace_and_isReduced X).mpr ⟨‹_›, ‹_›⟩
  have : A.IsSeparated := ⟨by rw [← terminal.comp_from fA]; infer_instance⟩
  let U₀ : X.Opens := u.opensRange
  have hU₀ne : (U₀ : Set X).Nonempty := ⟨u.base (Classical.arbitrary U), ⟨_, rfl⟩⟩
  have hU₀d : Dense (U₀ : Set X) := U₀.2.dense hU₀ne
  let e := u.isoOpensRange
  let φ₀ : (U₀ : Scheme.{u}) ⟶ A := e.inv ≫ φ
  have hι : e.hom ≫ U₀.ι = u := u.isoOpensRange_hom_ι
  have hι' : e.inv ≫ u = U₀.ι := u.isoOpensRange_inv_comp
  have hφ₀ : φ₀ ≫ fA = U₀.ι ≫ g := by
    change (e.inv ≫ φ) ≫ fA = U₀.ι ≫ g
    rw [Category.assoc, hφ, ← Category.assoc, hι']
  let pm : X.PartialMap A := ⟨U₀, hU₀d, φ₀⟩
  let r := pm.toRationalMap
  let : X.Over (Spec (CommRingCat.of k)) := ⟨g⟩
  let : A.Over (Spec (CommRingCat.of k)) := ⟨fA⟩
  have hpm : pm.IsOver (Spec (CommRingCat.of k)) := by
    rw [Scheme.PartialMap.isOver_iff, Scheme.PartialMap.compHom_hom]
    exact hφ₀
  have hr : r.IsOver (Spec (CommRingCat.of k)) := ⟨⟨pm, hpm, rfl⟩⟩
  let w := r.toPartialMap
  have hwover : w.IsOver (Spec (CommRingCat.of k)) :=
    Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated.mp
      (by rw [Scheme.RationalMap.toRationalMap_toPartialMap]; exact hr)
  have hw : w.hom ≫ fA = r.domain.ι ≫ g := by
    have h := Scheme.PartialMap.isOver_iff.mp hwover
    rwa [Scheme.PartialMap.compHom_hom] at h
  have hexist : ValuativeCriterion.Existence fA := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) fA := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1
  have hV1 : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ r.domain := fun x hx =>
    Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk g fA hexist pm hφ₀ x
      (valuationRing_stalk_of_ringKrullDim_le_one k g x hx)
  obtain ⟨W, d, hΔ, hrec⟩ :=
    exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
      k L g r.domain hV1 ⟨w.hom, hw⟩
  obtain ⟨ψ, hψ⟩ :=
    exists_extension_of_diagonal_difference_extension_of_dense
      k L g r.domain r.dense_domain ⟨w.hom, hw⟩ W d ⟨hΔ, hrec⟩
  refine ⟨ψ.1, ψ.2, ?_⟩
  have hUV : U₀ ≤ r.domain := pm.le_domain_toRationalMap
  have hres : X.homOfLE hUV ≫ w.hom = φ₀ := by
    exact Scheme.PartialMap.toPartialMap_toRationalMap_restrict pm
  have hψ' : r.domain.ι ≫ ψ.1 = w.hom := hψ
  calc u ≫ ψ.1 = e.hom ≫ U₀.ι ≫ ψ.1 := by rw [← Category.assoc, hι]
    _ = e.hom ≫ (X.homOfLE hUV ≫ r.domain.ι) ≫ ψ.1 := by rw [Scheme.homOfLE_ι]
    _ = e.hom ≫ X.homOfLE hUV ≫ w.hom := by rw [Category.assoc, hψ']
    _ = e.hom ≫ φ₀ := by rw [hres]
    _ = φ := e.hom_inv_id_assoc φ

end AlgebraicGeometry.WeilExtField.EXT

open _root_.AlgebraicCurves.Geometry.Picard.Proofs in
open exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle in
attribute [local instance]
  AlgebraicGeometry.WeilExtField.EXT.isDomain_sections_spec
open _root_.AlgebraicCurves.Geometry.Picard.Proofs in
open exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle in
attribute [local instance]
  AlgebraicGeometry.WeilExtField.EXT.isIntegrallyClosed_sections_spec




end

open _root_.AlgebraicCurves.Geometry.Picard.Proofs in
open exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle in
attribute [local instance]
  AlgebraicGeometry.WeilExtField.EXT.isDomain_sections_spec
open _root_.AlgebraicCurves.Geometry.Picard.Proofs in
open exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle in
attribute [local instance]
  AlgebraicGeometry.WeilExtField.EXT.isIntegrallyClosed_sections_spec


theorem _root_.AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
    {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [IsSeparated g] [QuasiCompact g] [IrreducibleSpace X]
    {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k fA)
    {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u] [Nonempty U]
    (φ : U ⟶ A) (hφ : φ ≫ fA = u ≫ g) :
    ∃ ψ : X ⟶ A, ψ ≫ fA = g ∧ u ≫ ψ = φ :=
  AlgebraicGeometry.WeilExtField.EXT.main g hA u φ hφ
end exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
end AlgebraicCurves.Geometry.Picard.Proofs
end ProofImplementation
