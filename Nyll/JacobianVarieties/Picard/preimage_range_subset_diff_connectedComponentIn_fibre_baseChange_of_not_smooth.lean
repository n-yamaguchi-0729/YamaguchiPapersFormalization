/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.ChartSections
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.JacobianVarieties.Picard.exists_fibreIso_hom_comp_eq

/-!
# Complements of fibre components after base change

The fibre comparison preserves the section point and the inverse image of the chosen open.
It transports containment outside the section's component on non-smooth fibres.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ComponentComplement

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Hom
  Scheme.homeoOfIso
  Spec
  Scheme
  Smooth
  Scheme.Hom.comp_preimage
  Scheme.Hom.comp_apply)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (sectionFibrePoint exists_fibreIso_hom_comp_eq)

namespace TZETransport

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A]

theorem exists_fibreIso_baseChange {k : Type u} [Field k]
    (x' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)) :
    ∃ φ : pullback (baseChange R c A) x' ≅ pullback c (x' ≫ specMap R A),
      φ.hom ≫ pullback.snd c (x' ≫ specMap R A) = pullback.snd (baseChange R c A) x' ∧
      φ.hom ≫ pullback.fst c (x' ≫ specMap R A) =
        pullback.fst (baseChange R c A) x' ≫ pullback.fst c (specMap R A) := by
  obtain ⟨φ, h1, h2, -⟩ := exists_fibreIso_hom_comp_eq c (specMap R A) x' (x' ≫ specMap R A) rfl
  exact ⟨φ, h1, h2⟩

end AlgebraicGeometry.RelPicard.TZETransport

open AlgebraicGeometry.RelPicard.TZETransport in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem preimage_range_subset_diff_connectedComponentIn_fibre_baseChange_of_not_smooth
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (U : C.Opens)
    {Z ZA : Scheme.{u}} (z : Z ⟶ C) (zA : ZA ⟶ pullback c (specMap R A))
    (hzA : Set.range (zA ≫ pullback.fst c (specMap R A)).base ⊆ Set.range z.base)
    (hz'ε : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      ¬ Smooth (pullback.snd c s) →
      (pullback.fst c s).base ⁻¹' Set.range z.base ⊆
        ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) : Set ↥(pullback c s)) \
          connectedComponentIn ((pullback.fst c s ⁻¹ᵁ U : (pullback c s).Opens) :
            Set ↥(pullback c s))
            (((sectionFibrePoint ε s).1).base (IsLocalRing.closedPoint k))) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A)),
      ¬ Smooth (pullback.snd (baseChange R c A) s') →
      (pullback.fst (baseChange R c A) s').base ⁻¹' Set.range zA.base ⊆
        ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
            (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) \
          connectedComponentIn
            ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
                (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s'))
            (((sectionFibrePoint (sectionBaseChange A ε) s').1).base
              (IsLocalRing.closedPoint k)) := by
  intro k _ _ s' hns
  obtain ⟨φ, hφ2, hφ1⟩ := exists_fibreIso_baseChange c A s'
  let e : ↥(pullback (baseChange R c A) s') ≃ₜ ↥(pullback c (s' ≫ specMap R A)) :=
    Scheme.homeoOfIso φ
  have hesymm : ∀ x : ↥(pullback c (s' ≫ specMap R A)), e.symm x = φ.inv.base x := fun _ => rfl
  have hV' : pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U)
      = φ.hom ⁻¹ᵁ (pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hφ1]
  have hV'set : ((pullback.fst (baseChange R c A) s' ⁻¹ᵁ (pullback.fst c (specMap R A) ⁻¹ᵁ U) :
      (pullback (baseChange R c A) s').Opens) : Set ↥(pullback (baseChange R c A) s')) =
      e ⁻¹' ((pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s' ≫ specMap R A)).Opens) :
        Set ↥(pullback c (s' ≫ specMap R A))) := by
    rw [hV']; rfl
  have hsec : (sectionFibrePoint (sectionBaseChange A ε) s').1 ≫ φ.hom =
    (sectionFibrePoint ε (s' ≫ specMap R A)).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ1]
      simp only [sectionFibrePoint, pullback.lift_fst_assoc, pullback.lift_fst,
        Category.assoc, sectionBaseChange_coe_fst]
    · rw [Category.assoc, hφ2]
      simp only [sectionFibrePoint, pullback.lift_snd]
  have hsecpt : φ.inv.base
      (((sectionFibrePoint ε (s' ≫ specMap R A)).1).base (IsLocalRing.closedPoint k))
      = ((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k) := by
    rw [← hsec]
    exact e.symm_apply_apply _
  set V : Set ↥(pullback c (s' ≫ specMap R A)) :=
    ((pullback.fst c (s' ≫ specMap R A) ⁻¹ᵁ U : (pullback c (s' ≫ specMap R A)).Opens) :
      Set ↥(pullback c (s' ≫ specMap R A)))
    with hVdef
  set pt := ((sectionFibrePoint ε (s' ≫ specMap R A)).1).base (IsLocalRing.closedPoint k)
    with hptdef
  have hcc : e ⁻¹' connectedComponentIn V pt =
      connectedComponentIn (e ⁻¹' V)
        (((sectionFibrePoint (sectionBaseChange A ε) s').1).base (IsLocalRing.closedPoint k)) := by
    rw [← hsecpt, ← hesymm]
    by_cases hx : pt ∈ V
    · rw [← Homeomorph.image_symm]
      exact Homeomorph.image_connectedComponentIn _ hx
    · rw [connectedComponentIn_eq_empty hx, Set.preimage_empty, connectedComponentIn_eq_empty]
      intro h
      apply hx
      have : e (e.symm pt) ∈ V := h
      rwa [e.apply_symm_apply] at this
  have hmove : ∀ p : ↥(pullback (baseChange R c A) s'),
      (pullback.fst (baseChange R c A) s').base p ∈ Set.range zA.base →
        e p ∈ (pullback.fst c (s' ≫ specMap R A)).base ⁻¹' Set.range z.base := by
    rintro p ⟨q, hq⟩
    change (pullback.fst c (s' ≫ specMap R A)).base (φ.hom.base p) ∈ Set.range z.base
    rw [← Scheme.Hom.comp_apply, hφ1, Scheme.Hom.comp_apply, ← hq]
    exact hzA ⟨q, rfl⟩
  have hns0 : ¬ Smooth (pullback.snd c (s' ≫ specMap R A)) := by
    intro h
    apply hns
    rw [← hφ2]
    infer_instance
  intro p hp
  have h1 := hz'ε k (s' ≫ specMap R A) hns0 (hmove p hp)
  have h2 : p ∈ e ⁻¹' (V \ connectedComponentIn V pt) := h1
  rw [Set.preimage_sdiff, hcc] at h2
  rw [hV'set]
  exact h2
end JacobianVarieties.Picard.Proofs.ComponentComplement
end ProofImplementation

attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp]
  AlgebraicGeometry.RelPicard.thetaBundle_def
  AlgebraicGeometry.RelPicard.picardBundle_def
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor
  AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I
  AlgebraicGeometry.mapOnProdOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec
  AlgebraicGeometry.RelEffCartierDiv.mk.injEq
  AlgebraicGeometry.mapOnProdOver_snd
  AlgebraicGeometry.mapOnProdOver_fst
  AlgebraicGeometry.mapOnProdOver_snd_assoc
  AlgebraicGeometry.mapOnProdOver_id
  AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_fst
  AlgebraicCurve.mapOnProd_fst_assoc
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.mapOnProd_snd_assoc
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
