/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.AbelJacobiDivisionDisplacement
import Nyll.JacobianVarieties.Kummer.MovingRepresentatives
import Nyll.JacobianVarieties.Kummer.WeilGenericCharacter
import Nyll.JacobianVarieties.WeilPairing.ConstantExtension
import Nyll.JacobianVarieties.Picard.ConstantExtensionFixedDivisors
import Nyll.JacobianVarieties.Pic0.Pic0_nonempty_divisorialWeilPairingData_of_isAlgClosed
import Nyll.AlgebraicCurves.Models.CurveModelGeometricGenericLift
import Nyll.AlgebraicCurves.Models.CurveModelGenericPointEvaluation
import Nyll.AlgebraicCurves.Models.CurveModelSemilinearFixedField
import Nyll.AlgebraicCurves.Geometry.Schemes.genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
import Nyll.AlgebraicCurves.Places.Place_evalAt_map_eq_of_comap_eq

/-!
# The actual Abel--Jacobi Weil character at the geometric generic point

This proof constructs the Kummer representative and the division divisor
from the actual Abel--Jacobi multiplication fibre. It derives the fixed
function, fixed divisor, evaluation and conorm identities before applying
the Weil reciprocity calculation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve AlgebraicCurve.CurveModel NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Pic0.Proofs.ConormInjectivity.AlgebraicCurve.ConDesc
open JacobianVarieties.WeilPairing
open AlgebraicCurves.Models.Proofs.UniquePointPullbackOrder.AlgebraicGeometry
open scoped Pointwise

namespace JacobianVarieties.Kummer

attribute [local instance]
  IsCurveOver.toHasPrincipalDivisors
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

/-- Actual Abel--Jacobi multiplication monodromy and the actual curve
Kummer character agree through the divisorial Weil pairing at the generic
point. All action and pairing comparisons are conclusions of geometry. -/
theorem exists_actual_abelJacobi_generic_weil_kummer
    {K F₀ : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀]
    (M₀ : CurveModel K F₀)
    [Algebra K M₀.C.functionField]
    (hbase : algebraMap K M₀.C.functionField = baseToFunctionField M₀.toBase)
    {Ω F : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra M₀.C.functionField Ω] [IsScalarTower K M₀.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M₀.C.functionField Ω]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    [Algebra F₀ F] [Algebra K F]
    [IsScalarTower K F₀ F] [IsScalarTower K Ω F]
    (hfg : ∃ t : F₀, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F₀)) F₀)
    (hfg' : ∃ t : F, Transcendental Ω t ∧
      FiniteDimensional (IntermediateField.adjoin Ω ({t} : Set F)) F)
    (hgen : IntermediateField.adjoin Ω (Set.range (algebraMap F₀ F)) = ⊤)
    [IsProper M₀.toBase] [SmoothOfRelativeDimension 1 M₀.toBase] [GeometricallyIntegral M₀.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase)
    (D : RelativePic0Designation K M₀.toBase)
    (hD : RepresentsRelSubPic M₀.toBase ε (algEquivZeroCut M₀.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M₀.toBase D.toBase)
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M₀.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M₀.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (M : CurveModel Ω F) (eC : M.C ≅ pullback M₀.toBase (specMap K Ω))
    (heC : eC.hom ≫ pullback.snd M₀.toBase (specMap K Ω) = M.toBase)
    (hsq : ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme
          ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U))]
        (r : Γ(M₀.C, U)),
      M.ffEquiv.symm (M.C.germToFunctionField
        ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)
        (((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)).app U).hom r)) =
      algebraMap F₀ F (M₀.ffEquiv.symm (M₀.C.germToFunctionField U r)))
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (w : DivisorialWeilPairingData K F₀ (n : ℕ))
    (a : Pic0.torsion K F₀ (n : ℕ)) :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M₀.toBase ε) hD
    let η := Spec.map (CommRingCat.ofHom (algebraMap M₀.C.functionField Ω))
    let q := M₀.C.fromSpecStalk (genericPoint M₀.C)
    ∀ (e₀ : Pic0 K F₀ ≃+ G.AlgPoints hc K)
      (τn : Pic0.torsion K F₀ (n : ℕ) ≃+
        ProCGroups.torsionLevel (G.AlgPoints hc K) n),
      (∀ t, (τn t).1 = e₀ t.1) →
      (∀ v : SchemeHomOver (𝟙 (Spec (.of K))) M₀.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F₀),
          (Dv : Divisor K F₀) = Finsupp.single (M₀.pointEquivPlace v) 1 -
            Finsupp.single (M₀.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e₀ (Pic0.mk Dv))).1 = v.1 ≫ aj.1) →
    ∀ (τ : FiniteEtale.fiber (η ≫ q ≫ aj.1) ≅
        FiniteEtale.fiber (G.one (𝟙 (Spec (.of K)))).1)
      (_ : (FiniteEtale.fiber (η ≫ q ≫ aj.1)).obj (G.multiplicationCover hc n)),
    ∃ u : Pic0.kummerUnits K F₀ n,
      Multiplicative.toAdd (Pic0.kummerClass n u) = a ∧
      ∀ σ : Ω ≃ₐ[M₀.C.functionField] Ω,
        w.pair a (τn.symm
          (G.multiplicationMonodromy hc n
            (continuousConjAut τ
              (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
                (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) σ))))) =
          ((M₀.kummerMonodromyCharacter n u hn (η ≫ q)
            (FiniteEtale.fundamentalGroupHom q η
              (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) σ)) : Kˣ) : K) := by
  intro G hc η q e₀ τn hτn hpoint₀ τ z
  classical
  have hfgcopy := hfg'
  obtain ⟨j, hj, hjfin⟩ := hfgcopy
  have hjrange : j ∉ Set.range (algebraMap Ω F) := by
    rintro ⟨c, rfl⟩
    exact hj (isAlgebraic_algebraMap c)
  obtain ⟨ρ, hρ⟩ := FunctionField.exists_ratFuncAlgHom_apply_X_eq hjrange
  let : Algebra (RatFunc Ω) F := ρ.toRingHom.toAlgebra
  have : IsScalarTower Ω (RatFunc Ω) F :=
    IsScalarTower.of_algebraMap_eq fun c => (ρ.commutes c).symm
  have : FiniteDimensional (RatFunc Ω) F :=
    JacobianVarieties.Pic0.Proofs.ClosedFieldWeilData.AlgebraicCurve.WC7P.finite_ratFunc_of_adjoin
      ρ hρ hjfin
  let p := eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)
  let φ : M₀.C.functionField →+* F :=
    (algebraMap F₀ F).comp M₀.ffEquiv.symm.toRingHom
  have hφ (U : M₀.C.Opens) [Nonempty U] [Nonempty (p ⁻¹ᵁ U)] (r : Γ(M₀.C, U)) :
      φ (M₀.C.germToFunctionField U r) =
        M.ffEquiv.symm (M.C.germToFunctionField (p ⁻¹ᵁ U) ((p.app U).hom r)) :=
    (hsq U r).symm
  have hι (k : K) : algebraMap M₀.C.functionField Ω (baseToFunctionField M₀.toBase k) =
      algebraMap K Ω k := by
    rw [← hbase]
    exact (IsScalarTower.algebraMap_apply K M₀.C.functionField Ω k).symm
  obtain ⟨x, hx⟩ := M₀.exists_geometricGenericPoint M eC heC
    (algebraMap M₀.C.functionField Ω) hι
  have hgeom := (
existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
      (algebraMap K Ω) M₀ M eC heC (algebraMap F₀ F) hsq)
  obtain ⟨s, hs, _⟩ := hgeom.1 ε
  have hslift : lift hfg hfg' hgen (M₀.pointEquivPlace ε) = M.pointEquivPlace s :=
    (eq_lift_of_comap_eq hfg hfg' hgen (hgeom.2.1 ε s hs).1).symm
  obtain ⟨Dv, u, hDv, havoid, hdiv, hu⟩ :=
    Pic0.exists_kummer_representative_avoiding n a {M₀.pointEquivPlace ε}
  have hf : (u.val : F₀) ≠ 0 := Units.ne_zero u.val
  have hDε₀ : (Dv : Divisor K F₀) (M₀.pointEquivPlace ε) = 0 := by
    by_contra h
    exact havoid _ (Finsupp.mem_support_iff.mpr h) (Finset.mem_singleton_self _)
  let Dc : Divisor Ω F := con hfg hfg' hgen (Dv : Divisor K F₀)
  let f : F := algebraMap F₀ F (u.val : F₀)
  have hfn : f ≠ 0 := (map_ne_zero _).mpr hf
  have hfdiv (v : Place Ω F) : v.ord f = (n : ℤ) * Dc v :=
    ord_map_eq_mul_con hfg hfg' hgen (n : ℕ) (Dv : Divisor K F₀) (u.val : F₀) hf hdiv v
  have hfx : (M.pointEquivPlace x).evalAt f =
      algebraMap M₀.C.functionField Ω (M₀.ffEquiv (u.val : F₀)) := by
    have h := M.evalAt_geometricGenericPoint p φ hφ
      (algebraMap M₀.C.functionField Ω) x hx (M₀.ffEquiv (u.val : F₀))
    change (M.pointEquivPlace x).evalAt
      (algebraMap F₀ F (M₀.ffEquiv.symm (M₀.ffEquiv (u.val : F₀)))) = _ at h
    rw [M₀.ffEquiv.symm_apply_apply] at h
    exact h
  have hDx : Dc (M.pointEquivPlace x) = 0 := by
    have ho := M.ord_geometricGenericPoint p φ hφ
      (algebraMap M₀.C.functionField Ω) x hx (M₀.ffEquiv (u.val : F₀))
      ((map_ne_zero _).mpr hf)
    have ho' : (M.pointEquivPlace x).ord f = 0 := by
      change (M.pointEquivPlace x).ord
        (algebraMap F₀ F (M₀.ffEquiv.symm (M₀.ffEquiv (u.val : F₀)))) = 0 at ho
      rw [M₀.ffEquiv.symm_apply_apply] at ho
      exact ho
    rw [hfdiv] at ho'
    exact (mul_eq_zero.mp ho').resolve_left (by exact_mod_cast n.ne_zero)
  have hDε : Dc (M.pointEquivPlace s) = 0 := by
    change con hfg hfg' hgen (Dv : Divisor K F₀) (M.pointEquivPlace s) = 0
    rw [← hslift, con_apply_lift, hDε₀]
  have hordε : (M₀.pointEquivPlace ε).ord (u.val : F₀) = 0 := by
    rw [hdiv, hDε₀, mul_zero]
  let b : K := (M₀.pointEquivPlace ε).evalAt (u.val : F₀)
  have hb : b ≠ 0 := (M₀.pointEquivPlace ε).evalAt_ne_zero_of_ord_eq_zero
    (M₀.isRational_pointEquivPlace ε) hf hordε
  have hcoeff (k : K) : algebraMap F₀ F (algebraMap K F₀ k) =
      algebraMap Ω F (algebraMap K Ω k) :=
    (IsScalarTower.algebraMap_apply K F₀ F k).symm.trans
      (IsScalarTower.algebraMap_apply K Ω F k)
  have hfε : (M.pointEquivPlace s).evalAt f =
      algebraMap M₀.C.functionField Ω (baseToFunctionField M₀.toBase b) := by
    rw [hι]
    exact Place.evalAt_map_eq_of_comap_eq (algebraMap K Ω) (algebraMap F₀ F) hcoeff
      (M₀.pointEquivPlace ε) (M.pointEquivPlace s) (hgeom.2.1 ε s hs).1
      (M₀.isRational_pointEquivPlace ε)
      ((M₀.pointEquivPlace ε).mem_toValuationSubring_of_ord_nonneg_alt hf hordε.ge)
  let uη : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap K M₀.C.functionField))) M₀.toBase :=
    ⟨q, (fromSpecStalk_generic_comp_toBase M₀.toBase).trans
      (congrArg (fun r : K →+* M₀.C.functionField => Spec.map (CommRingCat.ofHom r)) hbase).symm⟩
  obtain ⟨e, B, E, g, hpoint, hB, heE, hEavoid, hg, hgdiv, hacts⟩ :=
    JacobianVarieties.Picard.exists_abelJacobi_division_divisor_displacement
      hfg hfg' hgen M₀ ε D hD aj hclass M eC heC hsq uη x s hx hs n
      e₀ hpoint₀ τ z Dc.support
  have hDE (v : Place Ω F) : Dc v = 0 ∨ (E : Divisor Ω F) v = 0 := by
    by_cases h : Dc v = 0
    · exact Or.inl h
    · exact Or.inr (Finsupp.notMem_support_iff.mp
        (fun hv => hEavoid v hv (Finsupp.mem_support_iff.mpr h)))
  have hgdiv' (v : Place Ω F) :
      v.ord g = (n : ℤ) * (E : Divisor Ω F) v -
        (Finsupp.single (M.pointEquivPlace x) 1 +
          Finsupp.single (M.pointEquivPlace s) (-1) : Divisor Ω F) v := by
    simpa only [hB, sub_eq_add_neg, Finsupp.single_neg] using hgdiv v
  obtain ⟨w'⟩ := Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed Ω F hfg' (n : ℕ)
  refine ⟨u, hu, ?_⟩
  intro σ
  obtain ⟨θ, γ, hproj, hbaseγ, hγ, hfun, hplaces, hγB, hdisp⟩ := hacts σ
  have hp : p.base (genericPoint M.C) = genericPoint M₀.C := by
    have hgeneric : IsGenericPoint (p.base (genericPoint M.C)) Set.univ := by
      rw [isGenericPoint_iff_specializes]
      intro y
      simp only [Set.mem_univ, iff_true]
      rw [specializes_iff_forall_open]
      intro U hU hy
      exact genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
        (algebraMap K Ω).injective M₀.toBase eC.hom ⟨U, hU⟩ ⟨y, hy⟩
    exact (hgeneric.inseparable (genericPoint_spec M₀.C)).eq
  have hfix (r : F₀) : γ • algebraMap F₀ F r = algebraMap F₀ F r := by
    have h := M.semilinear_fixes_functionField_image p hp φ θ hproj γ hφ hfun (M₀.ffEquiv r)
    change γ • algebraMap F₀ F (M₀.ffEquiv.symm (M₀.ffEquiv r)) =
      algebraMap F₀ F (M₀.ffEquiv.symm (M₀.ffEquiv r)) at h
    rw [M₀.ffEquiv.symm_apply_apply] at h
    exact h
  have hγD : γ • Dc = Dc :=
    JacobianVarieties.Picard.constantExtension_divisor_fixed hfg hfg' hgen γ hfix Dv
  have hγB' : γ • (Finsupp.single (M.pointEquivPlace x) 1 +
      Finsupp.single (M.pointEquivPlace s) (-1) : Divisor Ω F) =
      Finsupp.single (M.pointEquivPlace x) 1 +
        Finsupp.single (M.pointEquivPlace s) (-1) := by
    rw [hB, sub_eq_add_neg, ← Finsupp.single_neg] at hγB
    exact hγB
  obtain ⟨d, hdL, hdR, _, _, hpair⟩ :=
    M₀.exists_weilDatum_pairing_eq_generic_kummer n u Dc E
      (M.pointEquivPlace x) (M.pointEquivPlace s) f g hfn hg hfdiv hgdiv'
      hDE hDx hDε b hb hfx hfε σ γ hγ (hfix (u.val : F₀)) hγD hγB' hn
  let t := G.multiplicationMonodromy hc n
    (continuousConjAut τ (FiniteEtale.fundamentalGroupHom (q ≫ aj.1) η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M₀.C.functionField] Ω) σ)))
  have ht : e₀.symm t.1 = (τn.symm t).1 := by
    apply e₀.injective
    rw [e₀.apply_symm_apply, ← hτn]
    exact congrArg Subtype.val (τn.apply_symm_apply t).symm
  have hdleft : d.classLeft = constantExtensionTorsion hfg hfg' hgen (n : ℕ) a := by
    apply Subtype.ext
    change Pic0.mk d.degZeroLeft = conPic0 hfg hfg' hgen a.1
    rw [← hDv, conPic0_mk]
    apply congrArg Pic0.mk
    apply Subtype.ext
    exact hdL
  have hdright : d.classRight =
      constantExtensionTorsion hfg hfg' hgen (n : ℕ) (τn.symm t) := by
    apply Subtype.ext
    change Pic0.mk d.degZeroRight = conPic0 hfg hfg' hgen (τn.symm t).1
    have hdE : d.degZeroRight = SemilinearAut.degZeroSMulHom γ E - E := by
      apply Subtype.ext
      exact hdR
    rw [hdE]
    change Pic0.mk (SemilinearAut.degZeroSMulHom γ E) - Pic0.mk E = _
    rw [← SemilinearAut.pic0_smul_mk]
    exact hdisp.trans (congrArg (conPic0 hfg hfg' hgen) ht)
  have hvalue := w'.compatible d
  rw [hdleft, hdright, pair_constantExtension hfg hfg' hgen w w'] at hvalue
  apply (algebraMap K Ω).injective
  calc
    algebraMap K Ω (w.pair a (τn.symm t)) = d.pairing := hvalue
    _ = _ := hpair.trans (hι _)
end JacobianVarieties.Kummer
