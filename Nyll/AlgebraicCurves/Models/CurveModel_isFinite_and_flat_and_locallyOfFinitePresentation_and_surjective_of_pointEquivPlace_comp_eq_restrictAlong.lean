/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import Nyll.AlgebraicCurves.Models.CurveModel_infinite_place
import Nyll.AlgebraicCurves.Geometry.Schemes.flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality

/-!
# Curve Model is Finite and flat and locally Of Finite Presentation and surjective of point
Equiv Place comp eq restrict Along
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.FiniteFlatCurveMap
open AlgebraicCurve.IsCurveOver in
attribute [-instance]
  instNontrivialKaehler
  instFreeKaehler
  toHasPrincipalDivisors
  instFiniteResidue
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
open _root_.AlgebraicCurve.RationalFunctionField in
attribute [-instance]
  instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

noncomputable section

namespace FF17

open TopologicalSpace

theorem finite_of_isClosed_of_forall_isClosed_singleton {α : Type*} [TopologicalSpace α]
  [NoetherianSpace α] [QuasiSober α]
    (Z : Set α) (hZ : IsClosed Z) (hpt : ∀ z ∈ Z, IsClosed ({z} : Set α)) : Z.Finite := by
  obtain ⟨S, hSfin, hSclosed, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hZ
  refine hSfin.sUnion fun t ht => (Set.finite_singleton (hSirr t ht).genericPoint).subset fun z hz
    => ?_
  have hgen := (hSirr t ht).isGenericPoint_genericPoint (hSclosed t ht)
  have hmem : (hSirr t ht).genericPoint ∈ t := hgen.mem
  have hcl := (hpt _ (Set.mem_sUnion_of_mem hmem ht)).closure_eq
  have hz' : z ∈ closure ({(hSirr t ht).genericPoint} : Set α) := by
    rw [hgen.def]; exact hz
  rwa [hcl] at hz'

theorem isClosed_singleton_base_of_isClosed {k : Type u} [Field k] [IsAlgClosed k] {X Y :
  Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX]
      [LocallyOfFiniteType fY]
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (x : X) (hx : IsClosed ({x} : Set X)) : IsClosed ({g.base x} :
      Set Y) := by
  let p := (pointEquivClosedPoint fX).symm ⟨x, hx⟩
  have hp : p.1.base (IsLocalRing.closedPoint k) = x :=
    congrArg Subtype.val ((pointEquivClosedPoint fX).apply_symm_apply ⟨x, hx⟩)
  have hq : (p.1 ≫ g) ≫ fY = 𝟙 _ := by rw [Category.assoc, hg, p.2]
  have h2 := (pointEquivClosedPoint fY ⟨p.1 ≫ g, hq⟩).2
  change IsClosed ({g.base (p.1.base (IsLocalRing.closedPoint k))} : Set Y) at h2
  rwa [hp] at h2

end FF17

end
end AlgebraicCurves.Models.Proofs.FiniteFlatCurveMap

namespace AlgebraicCurve.CurveModel

open _root_.AlgebraicCurves.Models.Proofs.FiniteFlatCurveMap
universe u v
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicCurve


open _root_.AlgebraicCurves.Models.Proofs.FiniteFlatCurveMap.FF17 in
theorem finite_flat_surjective_of_pointEquivPlace_comp_eq_restrictAlong
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [Algebra k F] [HasPrincipalDivisors k F] {F' : Type v} [Field F']
      [Algebra k F'] [HasPrincipalDivisors k F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (g : M'.C ⟶ M.C) (hg : g ≫ M.toBase = M'.toBase)
    (hgφ : ∀ x' : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨x'.1 ≫ g,
        by rw [Category.assoc, hg]; exact x'.2⟩ = (M'.pointEquivPlace x').restrictAlong φ hφ) :
    IsFinite g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g := by
  classical
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : IsProper g := by
    have : IsProper (g ≫ M.toBase) := by rw [hg]; infer_instance
    exact IsProper.of_comp g M.toBase
  have : IsLocallyNoetherian M'.C := LocallyOfFiniteType.isLocallyNoetherian M'.toBase
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : CompactSpace M'.C := by
    have h1 : QuasiCompact (Limits.terminal.from (Spec (CommRingCat.of k))) :=
      (compactSpace_iff_quasiCompact _).mp inferInstance
    have h2 : QuasiCompact (M'.toBase ≫ Limits.terminal.from _) := inferInstance
    rw [Limits.terminal.comp_from] at h2
    exact (compactSpace_iff_quasiCompact _).mpr h2
  have : IsNoetherian M'.C := {}
  have hres : ∀ y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨y.1 ≫ g,
        by rw [Category.assoc, hg]; exact y.2⟩ = (M'.pointEquivPlace y).restrict F := fun y => hgφ y
  have hbase : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _}),
      ((pointEquivClosedPoint M.toBase) ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩).1 =
        g.base (y.1.base (IsLocalRing.closedPoint k)) := by
    intro y
    change (y.1 ≫ g) (IsLocalRing.closedPoint k) =
      g (y.1 (IsLocalRing.closedPoint k))
    exact Scheme.Hom.comp_apply y.1 g (IsLocalRing.closedPoint k)
  have hgen : g.base (genericPoint M'.C) = genericPoint M.C := by
    by_contra hne
    have hz : IsClosed ({g.base (genericPoint M'.C)} : Set M.C) :=
      AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase _ hne
    have hall : ∀ x' : M'.C, g.base x' = g.base (genericPoint M'.C) := by
      intro x'
      have hs : g.base (genericPoint M'.C) ⤳ g.base x' :=
        ((genericPoint_spec M'.C).specializes (Set.mem_univ x')).map g.base.hom.continuous
      have := hs.mem_closure
      rw [hz.closure_eq, Set.mem_singleton_iff] at this
      exact this
    let z₀ : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
      (pointEquivClosedPoint M.toBase).symm ⟨g.base (genericPoint M'.C), hz⟩
    have hv : ∀ w : Place k F', w.restrict F = M.pointEquivPlace z₀ := by
      intro w
      let y := M'.pointEquivPlace.symm w
      have h1 := hres y
      rw [Equiv.apply_symm_apply] at h1
      rw [← h1]
      congr 1
      apply (pointEquivClosedPoint M.toBase).injective
      apply Subtype.ext
      rw [hbase y, hall]
      change _ = ((pointEquivClosedPoint M.toBase) ((pointEquivClosedPoint M.toBase).symm ⟨g.base
        (genericPoint M'.C), hz⟩)).1
      rw [Equiv.apply_symm_apply]
    have hfin : (Set.univ : Set (Place k F')).Finite :=
      (Place.restrict_fiber_finite (F' := F') (M.pointEquivPlace z₀)).subset fun w _ => hv w
    have := M'.infinite_place
    exact Set.infinite_univ hfin
  have hηnc : ¬ IsClosed ({genericPoint M.C} : Set M.C) := by
    intro hcl
    have huniv : (Set.univ : Set M.C) = {genericPoint M.C} := by
      rw [← (genericPoint_spec M.C).def, hcl.closure_eq]
    have := M.infinite_place
    have : (Set.univ : Set (Place k F)).Finite := by
      refine (Set.finite_singleton (M.pointEquivPlace ((pointEquivClosedPoint M.toBase).symm
        ⟨genericPoint M.C, hcl⟩))).subset ?_
      intro w _
      rw [Set.mem_singleton_iff]
      have hx := (pointEquivClosedPoint M.toBase (M.pointEquivPlace.symm w)).2
      have heq : (pointEquivClosedPoint M.toBase (M.pointEquivPlace.symm w)) = ⟨genericPoint M.C,
        hcl⟩ := by
        apply Subtype.ext
        have : ((pointEquivClosedPoint M.toBase (M.pointEquivPlace.symm w)).1 : M.C) ∈ (Set.univ :
          Set M.C) := Set.mem_univ _
        rwa [huniv, Set.mem_singleton_iff] at this
      have := congrArg (fun q => M.pointEquivPlace ((pointEquivClosedPoint M.toBase).symm q)) heq
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at this
      exact this
    exact Set.infinite_univ this
  have : LocallyQuasiFinite g := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    by_cases hzη : z = genericPoint M.C
    · subst hzη
      refine (Set.finite_singleton (genericPoint M'.C)).subset fun x hx => ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [Set.mem_singleton_iff]
      by_contra hxη
      have hxc : IsClosed ({x} : Set M'.C) := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
        M'.toBase x hxη
      have := isClosed_singleton_base_of_isClosed M'.toBase M.toBase g hg x hxc
      rw [hx] at this
      exact hηnc this
    · have hzc : IsClosed ({z} : Set M.C) := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
        M.toBase z hzη
      refine finite_of_isClosed_of_forall_isClosed_singleton _ (hzc.preimage g.base.hom.continuous)
        ?_
      intro x hx
      refine AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M'.toBase x fun hxη => hzη ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [← hx, hxη, hgen]
  have hfinite : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  have hsurj : Surjective g := ⟨by
    have hcl : IsClosed (Set.range g.base) := g.isClosedMap.isClosed_range
    have h : closure ({genericPoint M.C} : Set M.C) ⊆ Set.range g.base :=
      hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨_, hgen⟩)
    rw [(genericPoint_spec M.C).def] at h
    exact fun y => h (Set.mem_univ y)⟩
  have hY : ∀ y : M.C, IsIntegrallyClosed (M.C.presheaf.stalk y) := by
    intro y
    have hFk : IsField Γ(Spec (CommRingCat.of k), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
        (Field.toIsField k)
    let : Field Γ(Spec (CommRingCat.of k), ⊤) := hFk.toField
    have : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) := inferInstance
    have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
    exact (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase y).2
  have hdim : ∀ y : M.C, ringKrullDim (M.C.presheaf.stalk y) ≤ 1 := by
    intro y
    by_cases hyη : y = genericPoint M.C
    · subst hyη
      rw [ringKrullDim_eq_zero_of_field M.C.functionField]
      exact zero_le_one
    · have hyc : IsClosed ({y} : Set M.C) := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
        M.toBase y hyη
      let ψ : M.C.presheaf.stalk y →+* F :=
        (M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp (algebraMap (M.C.presheaf.stalk
          y) M.C.functionField)
      have hinj : Function.Injective ψ :=
        (M.ffEquiv.symm.injective).comp (IsFractionRing.injective (M.C.presheaf.stalk y)
          M.C.functionField)
      have hrange : ψ.range = (M.placeOfPoint ⟨y, hyc⟩).toValuationSubring.toSubring :=
        M.range_stalk_eq ⟨y, hyc⟩
      have hbij : Function.Bijective ψ.rangeRestrict :=
        ⟨fun a b h => hinj (congrArg Subtype.val h), ψ.rangeRestrict_surjective⟩
      let e : M.C.presheaf.stalk y ≃+* ↥(M.placeOfPoint ⟨y, hyc⟩).toValuationSubring :=
        (RingEquiv.ofBijective ψ.rangeRestrict hbij).trans (RingEquiv.subringCongr hrange)
      have : Ring.DimensionLEOne (M.C.presheaf.stalk y) := Ring.DimensionLEOne.of_ringEquiv e
      exact Ring.krullDimLE_iff.mp inferInstance
  obtain ⟨U, hU, hηU⟩ := M.finset_subset_affineOpen {genericPoint M.C}
  have : Nonempty U := ⟨⟨_, hηU _ (Finset.mem_singleton_self _)⟩⟩
  obtain ⟨hlfp, hflat, -⟩ :=
    AlgebraicGeometry.flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one g hY
      hdim U hU _ rfl
  exact ⟨hfinite, hflat, hlfp, hsurj⟩
end AlgebraicCurve.CurveModel
end ProofImplementation
