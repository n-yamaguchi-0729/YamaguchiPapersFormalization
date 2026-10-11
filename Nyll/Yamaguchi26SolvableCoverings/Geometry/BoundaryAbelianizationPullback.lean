/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot1AbelianInvariance
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot4FiniteEtaleStability
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenImmersionPullbackModel
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# 開正規部分群の上での境界アーベル化比較

定理 2.5 の幾何学的な段階。開正規部分群に対応する有限 étale 被覆とその引き戻しは
EFG の `OpenNormalPullbackModel` から実際に構成する。補題 2.1 と 2.4 によって
引き戻し全体が連結であることを示し、選んだ連結成分と境界補集合を同一視する。
その補集合に補題 2.1 を適用し、任意の有限離散可換群への連続準同型が局所的な核を
消すことを証明する。基本群の射の合成に伴う共役は、単位元に送られる条件を変えない。

この段階の証明は原稿の補題 2.1・2.4 に依存する。それらの証明が未完了である
限り、このファイルだけによって幾何学的な議論全体が完成したことにはならない。
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open ProCGroups.FiniteStepSolvableQuotients

namespace Yamaguchi26SolvableCoverings

private theorem finiteEtale_pullback_isEquivalence_of_isIso
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] :
    (pullback f).IsEquivalence := by
  let P : MorphismProperty Scheme.{0} := @IsFiniteEtale
  let e : Functor.fromPUnit X ≅ Functor.fromPUnit Y :=
    Discrete.natIso fun _ => asIso f
  let E : P.Over ⊤ X ≌ P.Over ⊤ Y :=
    MorphismProperty.Comma.mapRightIso (P := P) (Q := ⊤) (W := ⊤) (𝟭 Scheme) e
  have adj : E.functor ⊣ MorphismProperty.Over.pullback P ⊤ f :=
    MorphismProperty.Over.mapPullbackAdj P ⊤ f (P.of_isIso f) trivial
  exact (Functor.isEquivalence_iff_of_iso
    (E.toAdjunction.rightAdjointUniq adj)).mp
      (Equivalence.isEquivalence_inverse E)

private theorem fundamentalGroupHom_composite_eq_one
    {X Y Z : Scheme.{0}} {Ω : Type} [Field Ω]
    (f : X ⟶ Y) (g : Y ⟶ Z) (point : Spec (.of Ω) ⟶ X)
    (a : π₁ᵉᵗ(point)) (ha : fundamentalGroupHom (f ≫ g) point a = 1) :
    fundamentalGroupHom g (point ≫ f) (fundamentalGroupHom f point a) = 1 := by
  let hξ : (point ≫ f) ≫ g = point ≫ (f ≫ g) := Category.assoc point f g
  have hcomp := fundamentalGroupHom_comp_transport_eq_autHomOfCompIso
    f g (f ≫ g) rfl point (point ≫ (f ≫ g)) hξ a
  have hconj := autHomOfCompIso_eq_conj (pullback (f ≫ g))
    (pullbackFiberIso (f ≫ g) point)
    (pullbackCompositeFiberIsoOfEq f g (f ≫ g) rfl point (point ≫ (f ≫ g)) hξ) a
  rw [← hcomp] at hconj
  change hξ ▸ fundamentalGroupHom g (point ≫ f) (fundamentalGroupHom f point a) =
    MulAut.conj _ (fundamentalGroupHom (f ≫ g) point a) at hconj
  rw [ha, map_one] at hconj
  have transport_eq_one : ∀ {η η' : Spec (.of Ω) ⟶ Z} (h : η = η')
      (b : π₁ᵉᵗ(η)), (h ▸ b) = 1 → b = 1 := by
    intro η η' h b hb
    cases h
    exact hb
  exact transport_eq_one hξ _ hconj

/-- 条件 `(†)` の下で、開正規部分群の逆像から有限離散可換群への写像は境界核を消す。 -/
theorem boundary_openNormalFiniteDiscreteAbelianMapsKillKernel
    {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hD : BoundaryCondition D) [ConnectedSpace D.1.supportComplement]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (point : Spec (.of Ω) ⟶ D.1.supportComplement) :
    OpenNormalFiniteDiscreteAbelianMapsKillKernel
      (fundamentalGroupHom D.1.supportComplement.ι point) := by
  intro H
  let M := openNormalPullbackModel D.1.supportComplement.ι point H
  let D' : M.targetScheme.EffectiveCartierDivisor := D.comapFiniteEtale M.targetCover
  have hX : IsLocallyNoetherian
      ((Functor.fromPUnit X).obj M.targetCover.right) := by
    change IsLocallyNoetherian X
    infer_instance
  let : IsLocallyNoetherian M.targetScheme :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ M.targetCover.hom
      (inferInstance : LocallyOfFiniteType M.targetCover.hom) hX
  have hstability : IsHorizontal D' ∧ BoundaryCondition D' :=
    finite_etale_stability_2_4 D hhor hD M.targetCover
      (inferInstance : ConnectedSpace M.targetScheme)
  have hgeneric : HasGeometricallyIntegralGenericComponents D'.1 :=
    hD.2.2 M.targetCover (inferInstance : ConnectedSpace M.targetScheme)
  have hab := abelian_invariance_2_1 D' hstability.1
    hstability.2.1 hstability.2.2.1 hgeneric
  let : ConnectedSpace D'.1.supportComplement := hab.1
  obtain ⟨e, he⟩ : ∃ e : M.sourceScheme ≅ D'.1.supportComplement,
      e.hom ≫ D'.1.supportComplement.ι = M.hom := by
    let ep : ((pullback D.1.supportComplement.ι).obj M.targetCover).left ≅
        D'.1.supportComplement := pullbackSupportComplementIso D.1 M.targetCover
    let : ConnectedSpace ((pullback D.1.supportComplement.ι).obj M.targetCover).left :=
      ep.hom.homeomorph.connectedSpace_iff.mpr inferInstance
    let : IsConnected ((pullback D.1.supportComplement.ι).obj M.targetCover) :=
      isConnected_of_connectedSpace_left
        ((pullback D.1.supportComplement.ι).obj M.targetCover)
    let : IsGalois M.sourceCover := M.sourceIsGalois
    let : Mono M.inclusion := M.inclusionMono
    let : IsIso M.inclusion :=
      IsConnected.noTrivialComponent M.sourceCover M.inclusion
        (not_initial_of_inhabited (fiber point) M.sourcePoint)
    let : IsIso M.inclusion.hom :=
      (FiniteEtale.forget D.1.supportComplement).map_isIso M.inclusion
    let : IsIso M.inclusion.left :=
      (CategoryTheory.Over.forget (D.1.supportComplement : Scheme)).map_isIso
        M.inclusion.hom
    refine ⟨asIso M.inclusion.left ≪≫ ep, ?_⟩
    have hopen : ep.hom ≫ D'.1.supportComplement.ι =
        Limits.pullback.fst M.targetCover.hom D.1.supportComplement.ι := by
      change
        (pullbackRestrictIsoRestrict M.targetCover.hom D.1.supportComplement).hom ≫
          (M.targetCover.left.isoOfEq
            (D.1.supportComplement_comap M.targetCover.hom).symm).hom ≫
          D'.1.supportComplement.ι =
        Limits.pullback.fst M.targetCover.hom D.1.supportComplement.ι
      have hlast := Scheme.isoOfEq_hom_ι M.targetCover.left
        (D.1.supportComplement_comap M.targetCover.hom).symm
      exact
        (congrArg
          (fun k =>
            (pullbackRestrictIsoRestrict
              M.targetCover.hom D.1.supportComplement).hom ≫ k)
          hlast).trans
            (pullbackRestrictIsoRestrict_hom_ι _ _)
    simp only [Iso.trans_hom, asIso_hom, OpenNormalPullbackModel.hom,
      Category.assoc]
    rw [hopen]
  have hkill : ProCGroups.ProC.FiniteDiscreteAbelianMapsKillKernel
      (fundamentalGroupHom M.hom M.geometricPoint) := by
    let : (pullback e.hom).IsEquivalence :=
      finiteEtale_pullback_isEquivalence_of_isIso e.hom
    let eg : π₁ᵉᵗ(M.geometricPoint) ≃ₜ* π₁ᵉᵗ(M.geometricPoint ≫ e.hom) :=
      fundamentalGroupEquivOfPullbackEquivalence e.hom M.geometricPoint
    obtain ⟨eab, heab⟩ := hab.2 Ω (M.geometricPoint ≫ e.hom)
    intro A _ _ _ _ φ a ha
    let φ' : π₁ᵉᵗ(M.geometricPoint ≫ e.hom) →ₜ* A :=
      φ.comp (ContinuousMonoidHom.toContinuousMonoidHom eg.symm)
    have haComposite :
        fundamentalGroupHom (e.hom ≫ D'.1.supportComplement.ι) M.geometricPoint a = 1 := by
      rw [he]
      exact MonoidHom.mem_ker.mp ha
    have haComplement :
        fundamentalGroupHom D'.1.supportComplement.ι (M.geometricPoint ≫ e.hom)
          (eg a) = 1 :=
      fundamentalGroupHom_composite_eq_one e.hom D'.1.supportComplement.ι
        M.geometricPoint a haComposite
    have haAb : (QuotientGroup.mk (eg a) :
        TopologicalAbelianization π₁ᵉᵗ(M.geometricPoint ≫ e.hom)) = 1 := by
      apply eab.injective
      rw [heab, haComplement, QuotientGroup.mk_one, map_one]
    apply MonoidHom.mem_ker.mpr
    calc
      φ a = φ' (eg a) := by
        change φ a = φ (eg.symm (eg a))
        rw [eg.symm_apply_apply]
      _ = ProCGroups.Abelian.TopologicalAbelianization.lift φ'
          (QuotientGroup.mk (eg a)) := rfl
      _ = 1 := by
        rw [haAb]
        exact map_one _
  exact ProCGroups.ProC.finiteDiscreteAbelianMapsKillKernel_of_continuousMulEquiv
    (ProCGroups.ContinuousMonoidHom.restrictPreimage
      (fundamentalGroupHom D.1.supportComplement.ι point) (H : Subgroup π₁ᵉᵗ(point ≫
          D.1.supportComplement.ι)))
    (fundamentalGroupHom M.hom M.geometricPoint)
    M.sourceEquiv M.targetEquiv M.commutes hkill

end Yamaguchi26SolvableCoverings
