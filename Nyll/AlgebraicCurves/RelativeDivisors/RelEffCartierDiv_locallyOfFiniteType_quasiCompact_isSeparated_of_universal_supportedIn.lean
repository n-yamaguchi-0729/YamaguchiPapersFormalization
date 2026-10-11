/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivRestrict
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_IsUniversal_exists_sumMap
import Nyll.AlgebraicCurves.Foundations.CategoryTheory.CategoryTheory_MorphismProperty_widePullback_base
import Nyll.AlgebraicCurves.Geometry.Schemes.IsSeparated_of_comp_of_universallyClosed_of_surjective
import Nyll.AlgebraicCurves.Geometry.Schemes.LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective

/-!
# Rel Eff Cartier Div locally Of Finite Type quasi Compact is Separated of universal
supported In
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv

end RelEffCartierDiv_locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn
end AlgebraicCurves.RelativeDivisors.Proofs

namespace AlgebraicGeometry.RelEffCartierDiv

universe u

open _root_.AlgebraicCurves.RelativeDivisors.Proofs in
open RelEffCartierDiv_locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv in
theorem locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [IsLocallyNoetherian S] (U : 𝒞.Opens)
    [SmoothOfRelativeDimension 1 (U.ι ≫ f)] [QuasiCompact (U.ι ≫ f)] (r : ℕ)
    {Y : Scheme.{u}} (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (D : RelEffCartierDiv f r g), D.SupportedIn U →
      ∃! φ : {φ : T ⟶ Y // φ ≫ y = g}, PullsBackOver Duniv φ.1 φ.2 D) :
    LocallyOfFiniteType y ∧ QuasiCompact y ∧ IsSeparated y := by
  have hUV : U ≤ f ⁻¹ᵁ (⊤ : S.Opens) := le_top
  let ι : (↑(⊤ : S.Opens) : Scheme.{u}) ⟶ S := (⊤ : S.Opens).ι
  have : IsIso ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext1
    rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Scheme.Opens.range_ι,
      TopologicalSpace.Opens.coe_top]
  let fU := f.resLE ⊤ U hUV
  have hfU : fU ≫ ι = U.ι ≫ f := Scheme.Hom.resLE_comp_ι f hUV
  have hfU' : fU = (U.ι ≫ f) ≫ inv ι :=
    by rw [← hfU, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have : Smooth (U.ι ≫ f) := SmoothOfRelativeDimension.smooth (n := 1) (f := U.ι ≫ f)
  have : LocallyOfFiniteType (U.ι ≫ f) := inferInstance
  have : SmoothOfRelativeDimension 1 fU := by
    rw [hfU']; exact inferInstanceAs (SmoothOfRelativeDimension (1 + 0) ((U.ι ≫ f) ≫ inv ι))
  have : IsSeparated fU := by rw [hfU']; infer_instance
  have : QuasiCompact fU := by rw [hfU']; infer_instance
  have : LocallyOfFiniteType fU := by rw [hfU']; infer_instance
  have : IsLocallyNoetherian (↑(⊤ : S.Opens) : Scheme.{u}) := inferInstance
  let yU : Y ⟶ ↑(⊤ : S.Opens) := IsOpenImmersion.lift ι y
    (by rw [Scheme.Opens.range_ι]; exact fun _ _ => trivial)
  have hy : yU ≫ ι = y := IsOpenImmersion.lift_fac _ _ _
  let D' : RelEffCartierDiv fU r yU := restrictAlong f r ⊤ U hUV yU y hy Duniv hDunivU
  have hU' : D'.IsUniversal := by
    intro T gV E
    let E𝒞 := extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl E
    have hE𝒞 : E𝒞.SupportedIn U := extendAlong_supportedIn f r ⊤ U hUV gV (gV ≫ ι) rfl E
    obtain ⟨⟨φ, hφ⟩, hP, huq⟩ := huniv (gV ≫ ι) E𝒞 hE𝒞
    have hφV : φ ≫ yU = gV := by rw [← cancel_mono ι, Category.assoc, hy, hφ]
    have key : ∀ {A B : RelEffCartierDiv f r (gV ≫ ι)} (hA : A.SupportedIn U) (hB : B.SupportedIn
      U), A = B →
        restrictAlong f r ⊤ U hUV gV (gV ≫ ι) rfl A hA = restrictAlong f r ⊤ U hUV gV (gV ≫ ι) rfl
          B hB := by
      rintro A B hA hB rfl; rfl
    refine ⟨⟨φ, hφV⟩, ?_, ?_⟩
    · have h1 : Duniv.pullbackAlong φ hφ = E𝒞 := (hP.eq_pullbackAlong).symm
      have h2 : extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl (D'.pullbackAlong φ hφV) = E𝒞 := by
        rw [extendAlong_pullbackAlong f r ⊤ U hUV rfl hy D' φ hφV hφ]
        change (extendAlong f r ⊤ U hUV yU y hy (restrictAlong f r ⊤ U hUV yU y hy Duniv
          hDunivU)).pullbackAlong φ hφ = E𝒞
        rw [extendAlong_restrictAlong]; exact h1
      have h3 : D'.pullbackAlong φ hφV = E := by
        have hA := restrictAlong_extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl (D'.pullbackAlong φ hφV)
        have hB := restrictAlong_extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl E
        rw [← hA, ← hB]
        exact key _ _ h2
      rw [← h3]; exact pullsBackOver_pullbackAlong _ _ _
    · rintro ⟨ψ, hψ⟩ hPψ
      apply Subtype.ext
      change ψ = φ
      have hψ' : ψ ≫ y = gV ≫ ι := by rw [← hy, ← Category.assoc, hψ]
      have hE : E = D'.pullbackAlong ψ hψ := hPψ.eq_pullbackAlong
      have : PullsBackOver Duniv ψ hψ' E𝒞 := by
        have h4 : E𝒞 = Duniv.pullbackAlong ψ hψ' := by
          change extendAlong f r ⊤ U hUV gV (gV ≫ ι) rfl E = _
          rw [hE, extendAlong_pullbackAlong f r ⊤ U hUV rfl hy D' ψ hψ hψ']
          change (extendAlong f r ⊤ U hUV yU y hy (restrictAlong f r ⊤ U hUV yU y hy Duniv
            hDunivU)).pullbackAlong ψ hψ' = _
          rw [extendAlong_restrictAlong]
        rw [h4]; exact pullsBackOver_pullbackAlong _ _ _
      have := huq ⟨ψ, hψ'⟩ this
      exact congrArg Subtype.val this
  obtain ⟨σ, hσ, -, hfin, hflat, -, hsurj, -⟩ := hU'.exists_sumMap
  have := hfin; have := hflat; have := hsurj
  have hbase : ∀ (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange], P fU → P (fibrePowOver.toBase fU r) :=
    fun P _ _ hP => MorphismProperty.widePullback_base (P := P) (fun _ : Fin r => (↑U :
      Scheme.{u})) (fun _ => fU) fun _ => hP
  have hlft : LocallyOfFiniteType (σ ≫ yU) :=
    by rw [hσ]; exact hbase @LocallyOfFiniteType inferInstance
  have hqc : QuasiCompact (σ ≫ yU) := by rw [hσ]; exact hbase @QuasiCompact inferInstance
  have hsep : IsSeparated (σ ≫ yU) := by rw [hσ]; exact hbase @IsSeparated inferInstance
  have := hlft; have := hqc; have := hsep
  have h1 : LocallyOfFiniteType yU := LocallyOfFiniteType.of_comp_of_isFinite_of_flat_of_surjective
    σ yU
  have h2 : IsSeparated yU := IsSeparated.of_comp_of_universallyClosed_of_surjective σ yU
  have h3 : QuasiCompact yU := by
    refine ⟨fun W hWo hWc => ?_⟩
    have : yU ⁻¹' W = σ '' ((σ ≫ yU) ⁻¹' W) := by
      ext z; constructor
      · intro hz; obtain ⟨x, rfl⟩ := σ.surjective z; exact ⟨x, hz, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact hx
    rw [this]
    exact (QuasiCompact.isCompact_preimage _ hWo hWc).image σ.continuous
  rw [← hy]
  exact ⟨inferInstance, inferInstance, inferInstance⟩
end AlgebraicGeometry.RelEffCartierDiv
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
attribute [-simp] AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
