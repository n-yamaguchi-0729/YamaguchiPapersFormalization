/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_mul
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_comap_eq_of_supportedIn
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul

/-!
# Rel Eff Cartier Div exists supported In I eq mul of supported In
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
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
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn
    {𝒳 S : Scheme.{u}} {f : 𝒳 ⟶ S} [IsSeparated f] (U : 𝒳.Opens) [SmoothOfRelativeDimension 1 (U.ι
      ≫ f)]
    {r s : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) (E : RelEffCartierDiv f s g) (hD : D.SupportedIn U) (hE :
      E.SupportedIn U) :
    ∃ F : RelEffCartierDiv f (r + s) g, F.I = D.I * E.I ∧ F.SupportedIn U := by
  set j := pullback.map (U.ι ≫ f) g f g U.ι (𝟙 T) (𝟙 S) (by simp only [Category.comp_id])
    (by simp only [Category.comp_id, Category.id_comp]) with hj
  have hrange : Set.range ⇑j = (pullback.fst f g) ⁻¹' (U : Set 𝒳) := by
    rw [hj, Scheme.Pullback.range_map, Scheme.Opens.range_ι]
    ext x
    constructor
    · exact fun hx => hx.1
    · exact fun hx => ⟨hx, ⟨pullback.snd f g x, rfl⟩⟩
  have key : ∀ K : (pullback f g).IdealSheafData, (K.support : Set ↥(pullback f g)) ⊆ (pullback.fst
    f g) ⁻¹' (U : Set 𝒳) →
      (K.comap j).map j = K := by
    intro K hK
    have hZU : ∀ z : K.subscheme, K.subschemeι z ∈ Set.range ⇑j := by
      intro z
      rw [hrange]
      apply hK
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    have : IsIso (pullback.snd j K.subschemeι) := by
      refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
      ext z
      simp only [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rw [Scheme.Pullback.range_snd]
      exact hZU z
    change ((K.comap j).subschemeι ≫ j).ker = K
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition, ←
      Category.assoc,
      Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
  obtain ⟨DU, hDU⟩ := RelEffCartierDiv.exists_comap_eq_of_supportedIn U D hD
  obtain ⟨EU, hEU⟩ := RelEffCartierDiv.exists_comap_eq_of_supportedIn U E hE
  obtain ⟨FU, hFU⟩ := RelEffCartierDiv.exists_I_eq_mul DU EU
  obtain ⟨F, hFsupp, -, hFmap⟩ := RelEffCartierDiv.exists_supportedIn_comap_eq_of_isSeparated U FU
  refine ⟨F, ?_, hFsupp⟩
  have hsuppDE : ((D.I * E.I).support : Set ↥(pullback f g)) ⊆ (pullback.fst f g) ⁻¹' (U : Set 𝒳)
    := by
    intro x hx
    rw [Scheme.IdealSheafData.support_mul] at hx
    rcases hx with hx | hx
    · exact hD hx
    · exact hE hx
  calc F.I = FU.I.map j := hFmap
    _ = ((D.I * E.I).comap j).map j := by
        rw [hFU, hDU, hEU, Scheme.IdealSheafData.comap_mul]
    _ = D.I * E.I := key _ hsuppDE
end RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation
