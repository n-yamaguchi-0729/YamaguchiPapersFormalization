/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Nyll.JacobianVarieties.Picard.IsAlgEquivZero_of_iso_pointsSubBasepoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual

/-!
# Relative Picard varieties and fibre cohomology

Show that effective-divisor twist modules have algebraically trivial fibres.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.RelEffCartierDiv_isAlgEquivZero_twistModule_fibre

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem K2Aux.ker_comap_fst_eq_ofPoint_I {A B : Scheme.{u}} (a : A ⟶ B) [IsSeparated a]
    (P : B ⟶ A) (hP : P ≫ a = 𝟙 B) :
    P.ker.comap (pullback.fst a (𝟙 B)) = (RelEffCartierDiv.ofPoint a P hP).I := by
  have : IsClosedImmersion P := by
    have : IsClosedImmersion (P ≫ a) := by rw [hP]; infer_instance
    exact .of_comp P a
  rw [RelEffCartierDiv.ofPoint_I, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h : pullback.fst (pullback.fst a (𝟙 B)) P =
      pullback.snd (pullback.fst a (𝟙 B)) P ≫ graphOver a P hP := by
    apply pullback.hom_ext
    · rw [Category.assoc, graphOver_fst, pullback.condition]
    · rw [Category.assoc, graphOver_snd, Category.comp_id]
      rw [← Category.comp_id (pullback.snd a (𝟙 B)), ← pullback.condition, ← Category.assoc,
        pullback.condition, Category.assoc, hP, Category.comp_id]
  rw [h, Scheme.Hom.ker_comp_of_isIso]

theorem K2Aux.nonempty_iso_unit_of_subsingleton {X : Scheme.{u}} [Subsingleton X] [Nonempty X]
    {N : X.Modules} (hN : Scheme.Modules.IsInvertible N) :
    Nonempty (N ≅ 𝟙_ X.Modules) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hN.exists_trivialization (Classical.arbitrary X)
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun y _ => (Subsingleton.elim
    (Classical.arbitrary X) y) ▸ hxU
  refine ⟨?_⟩
  exact ((Scheme.Modules.pullbackId X).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr X.topIso.inv_hom_id.symm).app N ≪≫
    ((Scheme.Modules.pullbackComp X.topIso.inv X.topIso.hom).app N).symm ≪≫
    (Scheme.Modules.pullback X.topIso.inv).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso X.topIso.inv

section Fibre

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
  {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))

/-- The point of the fibre obtained by the graph of a point above the given base point. -/
noncomputable def K2Aux.fibrePt (q : Spec (CommRingCat.of k) ⟶ C) (hq : q ≫ c = x) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.snd c x) :=
  ⟨graphOver c q hq, graphOver_snd c q hq⟩

/-- The distinguished point of the fibre induced by the rigidifying section. -/
noncomputable def K2Aux.fibreBasePt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k)))
  (pullback.snd c x) :=
  ⟨RelPicard.rigSection c x ε, RelPicard.rigSection_snd ε x⟩

theorem K2Aux.nonempty_pullback_point_iso (q : Spec (CommRingCat.of k) ⟶ C) (hq : q ≫ c = x) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c x) (𝟙 _))).obj
        ((graphOver c q hq).ker.invModule ⊗ (RelPicard.sectionIdeal c ε x).module) ≅
      pointSubBasepointModule (a := pullback.snd c x) (K2Aux.fibrePt c x q hq)
        (K2Aux.fibreBasePt c ε x)) := by
  have hbase : MorphismProperty.IsStableUnderBaseChange
      (C := Scheme.{u}) (fun {_ _} f => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 (pullback.snd c x) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} f => SmoothOfRelativeDimension 1 f)
      (IsPullback.of_hasPullback c x) inferInstance
  set F := pullback.fst (pullback.snd c x) (𝟙 (Spec (CommRingCat.of k))) with hF
  have hq' : (graphOver c q hq).ker.comap F = (RelEffCartierDiv.ofPoint (pullback.snd c x) _
    (K2Aux.fibrePt c x q hq).2).I :=
    K2Aux.ker_comap_fst_eq_ofPoint_I _ _ _
  have hε' : (RelPicard.sectionIdeal c ε x).comap F = (RelEffCartierDiv.ofPoint
    (pullback.snd c x) _ (K2Aux.fibreBasePt c ε x).2).I :=
    K2Aux.ker_comap_fst_eq_ofPoint_I _ _ _
  have hIq : (graphOver c q hq).ker.IsInvertible := RelEffCartierDiv.isInvertible_I
    (RelEffCartierDiv.ofPoint c q hq)
  have hIq' : ((graphOver c q hq).ker.comap F).IsInvertible :=
    hq' ▸ RelEffCartierDiv.isInvertible_I _
  have hIε : (RelPicard.sectionIdeal c ε x).IsInvertible :=
    RelEffCartierDiv.isInvertible_I
      (RelEffCartierDiv.ofPoint c (x ≫ ε.1) (by rw [Category.assoc, ε.2, Category.comp_id]))
  have hIε' : ((RelPicard.sectionIdeal c ε x).comap F).IsInvertible :=
    hε' ▸ RelEffCartierDiv.isInvertible_I _
  obtain ⟨iq⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso F hIq hIq'
  let iε : (Scheme.Modules.pullback F).obj (RelPicard.sectionIdeal c ε x).module ≅
      ((RelPicard.sectionIdeal c ε x).comap F).module :=
    @asIso _ _ _ _ ((RelPicard.sectionIdeal c ε x).pullbackModuleComparison F)
      (Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison F hIε hIε')
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (?_ ⊗ᵢ ?_)⟩
  · exact iq ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hq')
  · exact iε ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module hε')

theorem K2Aux.nonempty_pullback_prod_iso (n : ℕ) (b : Fin n → (Spec (CommRingCat.of k) ⟶ C))
    (hb : ∀ i, b i ≫ c = x) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (pullback.snd c x) (𝟙 _))).obj
        ((prodKerGraph c b hb).invModule ⊗ ((RelPicard.sectionIdeal c ε x) ^ n).module) ≅
      pointsSubBasepointModule (a := pullback.snd c x) (K2Aux.fibreBasePt c ε x)
        (List.ofFn fun i => K2Aux.fibrePt c x (b i) (hb i))) := by
  induction n with
  | zero =>
    have h0 : prodKerGraph c b hb = ⊤ := prodKerGraph_zero c b hb
    have hJ : (RelPicard.sectionIdeal c ε x) ^ 0 = ⊤ := by
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    obtain ⟨e1⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso
      (Scheme.IdealSheafData.isInvertible_top (X := pullback c x))
    rw [List.ofFn_zero, pointsSubBasepointModule_nil]
    exact ⟨(Scheme.Modules.pullback _).mapIso
        ((eqToIso (congrArg Scheme.IdealSheafData.invModule h0) ⊗ᵢ
          eqToIso (congrArg Scheme.IdealSheafData.module hJ)) ≪≫ e1) ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _⟩
  | succ n ih =>
    obtain ⟨etail⟩ := ih (fun i => b i.succ) (fun i => hb i.succ)
    obtain ⟨ehead⟩ := K2Aux.nonempty_pullback_point_iso c ε x (b 0) (hb 0)
    have hsucc := prodKerGraph_succ c b hb
    have hJ : (RelPicard.sectionIdeal c ε x) ^ (n + 1) =
        RelPicard.sectionIdeal c ε x * (RelPicard.sectionIdeal c ε x) ^ n := pow_succ' _ _
    have hK0 : (graphOver c (b 0) (hb 0)).ker.IsInvertible :=
      RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (b 0) (hb 0))
    have hK' : (prodKerGraph c (fun i => b i.succ) (fun i => hb i.succ)).IsInvertible := by
      obtain ⟨D', hD'⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := c)
        (fun i => b i.succ) (fun i => hb i.succ)
      exact hD' ▸ RelEffCartierDiv.isInvertible_I D'
    have hJ1 : (RelPicard.sectionIdeal c ε x).IsInvertible :=
      RelEffCartierDiv.isInvertible_I
        (RelEffCartierDiv.ofPoint c (x ≫ ε.1) (by rw [Category.assoc, ε.2, Category.comp_id]))
    have hJn : ((RelPicard.sectionIdeal c ε x) ^ n).IsInvertible := hJ1.pow n
    obtain ⟨i1⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hK0 hK'
    obtain ⟨i2⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor hJ1 hJn
    rw [List.ofFn_succ, pointsSubBasepointModule_cons]
    exact ⟨(Scheme.Modules.pullback _).mapIso
        ((eqToIso (congrArg Scheme.IdealSheafData.invModule hsucc) ⊗ᵢ
            eqToIso (congrArg Scheme.IdealSheafData.module hJ)) ≪≫
          (i1 ⊗ᵢ i2) ≪≫ Scheme.Modules.tensorTensorTensorComm _ _ _ _) ≪≫
      Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (ehead ⊗ᵢ etail)⟩

end Fibre

theorem K2Aux.isAlgEquivZero_twistModule_of_isAlgClosed
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {r : ℕ}
    {k : Type u} [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (D : RelEffCartierDiv c r x) :
    IsAlgEquivZero (pullback.snd c x) (D.twistModule c ε) := by
  have hbase : MorphismProperty.IsStableUnderBaseChange
      (C := Scheme.{u}) (fun {_ _} f => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 (pullback.snd c x) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} f => SmoothOfRelativeDimension 1 f)
      (IsPullback.of_hasPullback c x) inferInstance
  have : LocallyOfFiniteType (pullback.snd c x) := by
    have : Smooth (pullback.snd c x) := SmoothOfRelativeDimension.smooth 1 _
    infer_instance
  obtain ⟨b, hb, hD⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed D
  obtain ⟨e⟩ := K2Aux.nonempty_pullback_prod_iso c ε x r b hb
  have hJ1 : (RelPicard.sectionIdeal c ε x).IsInvertible :=
    RelEffCartierDiv.isInvertible_I
      (RelEffCartierDiv.ofPoint c (x ≫ ε.1) (by rw [Category.assoc, ε.2, Category.comp_id]))
  have hX : IsAlgEquivZero (pullback.snd c x)
      (D.lineBundle ⊗ ((RelPicard.sectionIdeal c ε x) ^ r).module) :=
    IsAlgEquivZero.of_iso_pointsSubBasepoint (K2Aux.fibreBasePt c ε x) _
      ((Scheme.Modules.pullback _).mapIso
          (eqToIso (congrArg Scheme.IdealSheafData.invModule hD) ⊗ᵢ Iso.refl _) ≪≫ e)
  have hXinv : Scheme.Modules.IsInvertible
      (D.lineBundle ⊗ ((RelPicard.sectionIdeal c ε x) ^ r).module) :=
    (RelEffCartierDiv.isInvertible_I D).isInvertible_invModule.tensor
      (hJ1.pow r).isInvertible_module
  obtain ⟨eN⟩ := K2Aux.nonempty_iso_unit_of_subsingleton
    ((hXinv.pullback (RelPicard.rigSection c x ε)).dual).1
  have hqN : IsAlgEquivZero (pullback.snd c x)
      ((Scheme.Modules.pullback (pullback.snd c x)).obj
        (Scheme.Modules.dual ((Scheme.Modules.pullback (RelPicard.rigSection c x ε)).obj
          (D.lineBundle ⊗ ((RelPicard.sectionIdeal c ε x) ^ r).module)))) :=
    (IsAlgEquivZero.tensorUnit (pullback.snd c x)).of_iso
      ((Scheme.Modules.pullbackTensorUnitObjIso _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso eN.symm)
  rw [RelEffCartierDiv.twistModule_def, Scheme.Modules.rigidify_def]
  exact hX.tensor hqN

theorem K2Aux.isAlgEquivZero_twistModule_fibre'
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec
      (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) :
    IsAlgEquivZero (fibreAt c t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (D.twistModule c ε)) := by
  let ψ : SchemeHomOver (s ≫ t) t := ⟨s, rfl⟩
  have main := K2Aux.isAlgEquivZero_twistModule_of_isAlgClosed c ε (s ≫ t) (D.pullbackAlong ψ.1 ψ.2)
  obtain ⟨ebc⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε ψ D
  let e := pullbackLeftPullbackSndIso c t s
  have he1 : e.hom ≫ pullback.snd c (s ≫ t) = fibreAt c t s :=
    pullbackLeftPullbackSndIso_hom_snd c t s
  have he2 : e.hom ≫ RelPicard.baseChangeSnd c ψ = pullback.fst (pullback.snd c t) s := by
    apply pullback.hom_ext
    · simp only [RelPicard.baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id, e,
        pullbackLeftPullbackSndIso_hom_fst]
    · simp only [RelPicard.baseChangeSnd, Category.assoc, pullback.lift_snd, e,
        pullbackLeftPullbackSndIso_hom_snd_assoc, ψ, pullback.condition]
  refine ((main.of_iso ebc).pullback e.hom he1).of_iso ?_
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr he2).app _

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isAlgEquivZero_twistModule_fibre
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec
      (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {r : ℕ} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (D : RelEffCartierDiv c r t)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) :
    IsAlgEquivZero (fibreAt c t s)
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj (D.twistModule c ε)) :=
  AlgebraicGeometry.K2Aux.isAlgEquivZero_twistModule_fibre' c ε D k s
end JacobianVarieties.Picard.Proofs.RelEffCartierDiv_isAlgEquivZero_twistModule_fibre
end ProofImplementation

attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
attribute [-instance] AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
attribute [-instance] AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ
attribute [-instance] PresheafOfModules.pushforward_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_η
attribute [-instance] PresheafOfModules.free_monoidal
attribute [-instance] PresheafOfModules.restrictScalars_laxMonoidal
attribute [-instance] PresheafOfModules.PullbackMonoidal.isIso_δ_gS
attribute [-instance] PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb)
in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance] PresheafOfModules.pullback_monoidal'
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom
  (instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop)
in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom
  (instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop)
in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
attribute [-instance] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
attribute [-simp] AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons
  AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil
  AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc
attribute [-simp] AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
