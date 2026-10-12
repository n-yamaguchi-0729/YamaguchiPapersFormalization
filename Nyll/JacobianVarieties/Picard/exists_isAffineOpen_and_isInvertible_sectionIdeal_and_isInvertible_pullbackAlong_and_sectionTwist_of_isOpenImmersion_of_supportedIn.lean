/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_isAffineOpen_of_finset_of_universal_supportedIn
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_isAffineOpen_le_inf_forall_mem_of_finset
import Nyll.AlgebraicCurves.Geometry.Picard.isInvertible_sectionIdeal_of_range_subset
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I_of_supportedIn
import Nyll.JacobianVarieties.Picard.nonempty_pullback_sectionTwist_iso_of_range_subset
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.SchemeTheory.LocalGeometry.LocalRepresentabilityULift
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
/-!
# Affine neighbourhoods and invertible ideals for supported divisors

Universal supported divisors provide affine neighbourhoods of finite sets in the
charts. The section and divisor ideals are invertible, and section twists commute
with the given base changes inside the relative smooth locus.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.SupportedAffineInvertibility
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp]
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

universe u

open  CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem exists_affineCover_invertible_ideals_and_sectionTwist_pullback_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    (hcov : ∀ (V : (Spec (CommRingCat.of R)).affineOpens) (F : Finset ↥U),
      (∀ x ∈ F, (U.ι ≫ c) x ∈ (V : (Spec (CommRingCat.of R)).Opens)) →
      ∃ W : (↑U : Scheme.{u}).Opens, IsAffineOpen W ∧
        W ≤ (U.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧
        ∀ x ∈ F, x ∈ W)
    (r g e : ℕ)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (Duniv : RelEffCartierDiv c g y)
    (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R))
      (D : RelEffCartierDiv c g g'), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver Duniv φ.1 φ.2 D)
    {ι : Type u} (X : ι → Scheme.{u})
    (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶
      (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal)
    (hj : ∀ i, ∃ j : X i ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv (f i)).1)
    (Dγ : ι → RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hDγU : ∀ i, (Dγ i).SupportedIn U) :
    (∀ (i : ι) (F : Finset (X i)), ∃ U : (X i).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
    (∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)), (sectionIdeal c ε t).IsInvertible) ∧
    (∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)),
      ((Dγ i).pullbackAlong t (Category.comp_id t)).I.IsInvertible) ∧
    (∀ ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver t' t),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (sectionTwist c ε t r) ≅
        sectionTwist c ε t' r)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i F
    obtain ⟨j, hjopen, -⟩ := hj i
    have := hjopen
    obtain ⟨W, hW, -, hFW⟩ :=
      RelEffCartierDiv.exists_isAffineOpen_of_finset_of_universal_supportedIn c U hcov g y Duniv
        hDunivU huniv ⟨⊤, isAffineOpen_top _⟩ (F.image j.base) (fun p _ => trivial)
    obtain ⟨W', hW', hW'le, hFW'⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_le_inf_forall_mem_of_finset
        W hW j.opensRange (F.image j.base) hFW
        (fun p hp => by
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
          exact ⟨x, rfl⟩)
    refine ⟨j ⁻¹ᵁ W', ?_, fun x hx => hFW' _ (Finset.mem_image_of_mem _ hx)⟩
    have hle : W' ≤ j.opensRange := hW'le.trans inf_le_right
    have himg : j ''ᵁ (j ⁻¹ᵁ W') = W' := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr hle
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion j, himg]
    exact hW'
  · intro T t
    exact AlgebraicGeometry.RelPicard.isInvertible_sectionIdeal_of_range_subset c ε U hεU t
  · intro i T t
    exact AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_of_supportedIn (f := c) U _
      ((hDγU i).pullbackAlong t (Category.comp_id t))
  · intro T T' t t' ψ
    exact nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hεU ψ r
end JacobianVarieties.Picard.Proofs.SupportedAffineInvertibility
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp]
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
