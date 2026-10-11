/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_isUniversal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Sites.Representability
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isSheaf_functor
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isRepresentable_supportedIn
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_supportedIn_of_forall_finset

/-!
Existence of a universal relative effective Cartier divisor.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_isUniversal
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
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
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
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

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

open AlgebraicGeometry _root_.AlgebraicGeometry.RelEffCartierDiv in
theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y), Duniv.IsUniversal := by
  classical
  let F : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
    ⟨RelEffCartierDiv.functor f r, (isSheaf_iff_isSheaf_of_type _ _).2
      (RelEffCartierDiv.isSheaf_functor f r)⟩
  let ι : Type u := Σ V : S.affineOpens, {U : 𝒞.affineOpens // (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)}
  have hrep : ∀ i : ι, ∃ X : Scheme.{u},
      Nonempty ((RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).toFunctor.RepresentableBy X) :=
    fun i => by
      obtain ⟨X, -, hX⟩ := RelEffCartierDiv.isRepresentable_supportedIn f r i.1 i.2.1 i.2.2
      exact ⟨X, hX⟩
  choose X hX using hrep
  let e : ∀ i : ι, yoneda.obj (X i) ≅ (RelEffCartierDiv.supportedIn f r (i.2.1 :
    𝒞.Opens)).toFunctor :=
    fun i => Functor.representableByEquiv (hX i).some
  let fam : ∀ i : ι, yoneda.obj (X i) ⟶ F.1 :=
    fun i => (e i).hom ≫ (RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).ι
  have hfam : ∀ i, IsOpenImmersion.presheaf (fam i) := fun i =>
    (MorphismProperty.cancel_left_of_respectsIso _ _ _).2
      (RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl f r _)
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc fam) := by
    constructor
    rintro T ⟨g, D⟩
    rw [Scheme.mem_grothendieckTopology_iff]
    choose W hW V U hUV hsupp using
      fun t : T => RelEffCartierDiv.exists_supportedIn_of_forall_finset f hcov r D t
    refine ⟨Scheme.Cover.mkOfCovers T (fun t => (W t : Scheme.{u})) (fun t => (W t).ι)
      (fun t => ⟨t, ⟨t, hW t⟩, rfl⟩) (fun t => inferInstance), ?_⟩
    rintro Y q ⟨t⟩
    let i : ι := ⟨V t, ⟨U t, hUV t⟩⟩
    let sec : (RelEffCartierDiv.supportedIn f r (i.2.1 : 𝒞.Opens)).toFunctor.obj (op (W t :
      Scheme.{u})) :=
      ⟨(RelEffCartierDiv.functor f r).map (W t).ι.op ⟨g, D⟩, hsupp t⟩
    refine ⟨(Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec), ?_⟩
    have h1 : (Limits.Sigma.desc fam).app (op (W t : Scheme.{u}))
        ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec)) =
        (fam i).app _ ((e i).inv.app _ sec) := by
      rw [← types_comp_apply ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _)
          ((Limits.Sigma.desc fam).app _),
        ← NatTrans.comp_app, Limits.Sigma.ι_comp_desc]
    change (Limits.Sigma.desc fam).app (op (W t : Scheme.{u}))
        ((Limits.Sigma.ι (fun i => yoneda.obj (X i)) i).app _ ((e i).inv.app _ sec)) =
      (RelEffCartierDiv.functor f r).map (W t).ι.op ⟨g, D⟩
    rw [h1]
    change ((e i).inv.app _ ≫ (e i).hom.app _ ≫ (RelEffCartierDiv.supportedIn f r _).ι.app _)
      sec = _
    rw [Iso.inv_hom_id_app_assoc]
    rfl
  have hR : (RelEffCartierDiv.functor f r).IsRepresentable :=
    Scheme.LocalRepresentability.isRepresentable hfam
  exact (RelEffCartierDiv.isRepresentable_functor_iff f r).1 hR
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_isUniversal
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
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
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
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
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
