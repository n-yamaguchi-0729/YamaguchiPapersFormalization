/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_free_and_finrank_quotient_span_of_generates_ker_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id

/-!
# Sections of a power of the ideal of a curve section

A generator of a power of the ideal of a section of a smooth proper curve gives
a free quotient of affine sections with the rank prescribed by that power.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_free_and_finrank_quotient_span_of_generates_ker_pow
open
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
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
  AlgebraicCurve.mapOnProd_snd
  AlgebraicCurve.UnivDivisorPack.mk.injEq
  AlgebraicCurve.RelEffDivisor.mk.injEq
  AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
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
attribute [-simp]
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ORDERRANK

theorem main
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (V : C.Opens) (hV : IsAffineOpen V) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V) (g : Γ(C, V))
    (hg : ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
      (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g}) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    Module.Free R (Γ(C, V) ⧸ Ideal.span {g}) ∧ Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m := by
  let algV := Scheme.TwoAffineOpenCover.algebraOfHom c V
  let I : C.IdealSheafData := ε.1.ker ^ m
  let Z := I.subscheme
  let ι : Z ⟶ C := I.subschemeι
  obtain ⟨hfin, hrank, hflat, -⟩ :=
    AlgebraicGeometry.Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (p :=
        c) ε.1 ε.2 m
  change IsFinite (ι ≫ c) at hfin
  change ∀ t, (ι ≫ c).finrank t = m at hrank
  change Flat (ι ≫ c) at hflat
  have := hfin
  have := hflat
  have : IsClosedImmersion (ε.1 ≫ c) := by rw [ε.2]; infer_instance
  have : IsClosedImmersion ε.1 := IsClosedImmersion.of_comp ε.1 c
  have hsupp : (I.support : Set C) = Set.range ε.1.base := by
    change ((ε.1.ker ^ m).support : Set C) = _
    rw [Scheme.IdealSheafData.support_pow _ m (by omega), Scheme.Hom.support_ker,
      ε.1.isClosedEmbedding.isClosed_range.closure_eq]
  have hZV : (⊤ : Z.Opens) ≤ ι ⁻¹ᵁ V := by
    intro z _
    change ι.base z ∈ V
    apply hεV
    rw [← hsupp, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  let W : C.affineOpens := ⟨V, hV⟩
  have hIV : I.ideal W = Ideal.span {g} := by
    have := hg W le_rfl
    have hid : (C.presheaf.map (homOfLE (le_rfl : (W : C.Opens) ≤ V)).op).hom g = g := by
      have : homOfLE (le_rfl : (W : C.Opens) ≤ V) = 𝟙 _ := Subsingleton.elim _ _
      rw [this, op_id, CategoryTheory.Functor.map_id]; rfl
    rw [hid] at this
    exact this
  have : IsAffine Z := isAffine_of_isAffineHom (ι ≫ c)
  have hcmp := IsAffineOpen.SpecMap_appLE_fromSpec (ι ≫ c) (isAffineOpen_top _) (isAffineOpen_top Z)
    (le_top : (⊤ : Z.Opens) ≤ (ι ≫ c) ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at hcmp
  have happ : (ι ≫ c).appLE ⊤ ⊤ le_top = c.appLE ⊤ V le_top ≫ ι.appLE V ⊤ hZV :=
    (Scheme.Hom.appLE_comp_appLE ι c ⊤ V ⊤ le_top hZV).symm
  have happ2 : ι.appLE V ⊤ hZV = ι.app V ≫ Z.presheaf.map (homOfLE hZV).op := rfl
  have happ3 : ι.app V = CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal W)) ≫ (I.subschemeObjIso
      W).inv :=
    I.subschemeι_app W
  have htop : ι ⁻¹ᵁ V = ⊤ := le_antisymm le_top hZV
  have : IsIso (Z.presheaf.map (homOfLE hZV).op) := by
    have : homOfLE hZV = eqToHom htop.symm := Subsingleton.elim _ _
    rw [this, eqToHom_op]
    infer_instance
  let A' := Γ(C, V) ⧸ I.ideal W
  have halg : CommRingCat.ofHom (algebraMap R A') =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ V le_top) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal W)) := by
    ext r
    rfl
  let ψ : CommRingCat.of A' ⟶ Γ(Z, ⊤) := (I.subschemeObjIso W).inv ≫ Z.presheaf.map (homOfLE hZV).op
  have : IsIso ψ := IsIso.comp_isIso
  have hkey : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ι ≫ c).appLE ⊤ ⊤ le_top =
      CommRingCat.ofHom (algebraMap R A') ≫ ψ := by
    change _ = _ ≫ ((I.subschemeObjIso W).inv ≫ Z.presheaf.map (homOfLE hZV).op)
    rw [happ, happ2, happ3, halg]
    simp only [Category.assoc]
  have hιc : ι ≫ c = (Z.isoSpec.hom ≫ Spec.map ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R
      A')) := by
    have h1 : Z.isoSpec.inv ≫ (ι ≫ c) =
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (ι ≫ c).appLE ⊤ ⊤ le_top) := by
      rw [Spec.map_comp, hcmp]
    rw [hkey, Spec.map_comp] at h1
    rw [Category.assoc, ← h1, Iso.hom_inv_id_assoc]
  have : MorphismProperty.RespectsIso
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => IsFinite f) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => IsFinite f)
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => Flat f) :=
    Flat.isStableUnderBaseChange
  have : MorphismProperty.RespectsIso
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => Flat f) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => Flat f)
  have hfinA : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A'))) := by
    have := hfin; rw [hιc] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite _ _).mp this
  have hflatA : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A'))) := by
    have := hflat; rw [hιc] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @Flat _ _).mp this
  have : Module.Finite R A' := by
    have := (IsFinite.SpecMap_iff _).mp hfinA
    exact (RingHom.finite_algebraMap).mp this
  have : Module.Flat R A' := by
    have := (Flat.SpecMap_iff).mp hflatA
    exact (RingHom.flat_algebraMap_iff).mp this
  have : Module.Free R A' := Module.free_of_flat_of_isLocalRing
  have hrankA : Module.finrank R A' = m := by
    have h := hrank (IsLocalRing.closedPoint R)
    rw [hιc, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free] at h
    exact h
  let e : A' ≃ₐ[R] Γ(C, V) ⧸ Ideal.span {g} := Ideal.quotientEquivAlgOfEq R hIV
  refine ⟨Module.Free.of_equiv e.toLinearEquiv, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq, hrankA]

end ORDERRANK

open scoped TensorProduct in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
    NeronModelInfra in
theorem
    _root_.AlgebraicGeometry.SmoothProperCurve.free_and_finrank_quotient_span_of_generates_ker_pow
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (m : ℕ) (hm : 1 ≤ m)
    (V : C.Opens) (hV : IsAffineOpen V) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V) (g : Γ(C, V))
    (hg : ∀ W : C.affineOpens, ∀ hW : (W : C.Opens) ≤ V,
      (ε.1.ker ^ m).ideal W = Ideal.span {(C.presheaf.map (homOfLE hW).op).hom g}) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    Module.Free R (Γ(C, V) ⧸ Ideal.span {g}) ∧ Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m :=
  ORDERRANK.main R c ε m hm V hV hεV g hg
end SmoothProperCurve_free_and_finrank_quotient_span_of_generates_ker_pow
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
