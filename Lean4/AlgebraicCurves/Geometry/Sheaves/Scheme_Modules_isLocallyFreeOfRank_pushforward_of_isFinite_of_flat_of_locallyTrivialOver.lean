/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PullbackMonoidal
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_pushforward_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_tilde
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsLocallyFreeOfRank_of_iso
import Mathlib.Util.WithWeakNamespace

/-!
# Local freeness of a finite flat pushforward

Constructs local trivializations of the pushforward from local trivializations on a finite
flat cover.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.TensorProduct

namespace Ws31X1

open AlgebraicGeometry.Scheme.Modules

section affine

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

/-- The two-chart affine cover consisting of the whole affine scheme in both charts. -/
noncomputable def trivCover (X : Scheme.{u}) [IsAffine X] : X.TwoAffineOpenCover where
  U0 := ⊤
  U1 := ⊤
  isAffineOpen_U0 := isAffineOpen_top X
  isAffineOpen_U1 := isAffineOpen_top X
  sup_eq_top := sup_top_eq _
  isAffineOpen_inf := by rw [inf_idem]; exact isAffineOpen_top X

/-- The pushforward of the unit module along the given map of affine schemes. -/
noncomputable abbrev M₀ : (Spec A).Modules :=
  (Scheme.Modules.pushforward (Spec.map φ)).obj (𝟙_ (Spec B).Modules)

/-- The module of global sections of the pushed-forward unit module over the source ring. -/
noncomputable abbrev P₀ : ModuleCat.{u} A :=
  (modulesSpecToSheaf.obj (M₀ φ)).presheaf.obj (op ⊤)

theorem isIso_fromTildeΓ : IsIso (Scheme.Modules.fromTildeΓ (R := A) (M₀ φ)) := by
  have h := isIso_fromTildeGamma_pushforward_of_locallyTrivial (A := A) (Spec.map φ) (trivCover
    (Spec B))
    (𝟙_ (Spec B).Modules) (fun x => ⟨⊤, trivial, ⟨pullbackTensorUnitObjIso (⊤ : (Spec B).Opens).ι⟩⟩)
  exact h

/-- The target ring viewed as the underlying type of its module over the source ring. -/
def Bmod (_φ : A ⟶ B) : Type u := B
noncomputable scoped instance : CommRing (Bmod φ) := inferInstanceAs (CommRing B)
noncomputable scoped instance algB : Algebra A (Bmod φ) := φ.hom.toAlgebra

lemma algebraMap_Bmod (a : A) : algebraMap A (Bmod φ) a = (φ.hom a : B) := rfl

theorem smul_P₀ (a : A) (s : P₀ φ) :
    (show Γ(Spec B, ⊤) from a • s) = (show Γ(Spec B, ⊤) from (Spec.map φ).appTop ((Scheme.ΓSpecIso
      A).inv a)) * (show Γ(Spec B, ⊤) from s) := by
  change (show Γ(Spec B, ⊤) from (Spec.map φ).app ⊤ ((Spec A).ringCatSheaf.obj.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤))
        ((StructureSheaf.globalSectionsIso A).hom a))) *
    (show Γ(Spec B, ⊤) from s) = _
  rw [Subsingleton.elim ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op (⊤ : (Spec
    A).Opens))) (𝟙 _),
    CategoryTheory.Functor.map_id]
  rfl

theorem exists_linearEquiv : Nonempty (P₀ φ ≃ₗ[A] Bmod φ) := by
  have hnat : ∀ a : A, (Scheme.ΓSpecIso B).hom ((Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a)) =
    φ.hom a := by
    intro a
    have h := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality φ)
      ((Scheme.ΓSpecIso A).inv a)
    change (Scheme.ΓSpecIso B).hom ((Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a))
      = φ.hom ((Scheme.ΓSpecIso A).hom ((Scheme.ΓSpecIso A).inv a)) at h
    rw [Iso.inv_hom_id_apply] at h
    exact h
  refine ⟨{ toFun := fun s => (show Bmod φ from (Scheme.ΓSpecIso B).hom (show Γ(Spec B, ⊤) from s))
            invFun := fun b => (show P₀ φ from (show Γ(Spec B, ⊤) from (Scheme.ΓSpecIso B).inv
              (show B from b)))
            map_add' := fun s s' =>
              (Scheme.ΓSpecIso B).hom.hom.map_add
                (show Γ(Spec B, ⊤) from s) (show Γ(Spec B, ⊤) from s')
            map_smul' := fun a s => by
              change (Scheme.ΓSpecIso B).hom (show Γ(Spec B, ⊤) from a • s) = φ.hom a *
                (Scheme.ΓSpecIso B).hom _
              rw [smul_P₀, map_mul, hnat]
            left_inv := fun s => by
              change (show P₀ φ from (show Γ(Spec B, ⊤) from
                (Scheme.ΓSpecIso B).inv ((Scheme.ΓSpecIso B).hom (show Γ(Spec B, ⊤) from s)))) = s
              rw [Iso.hom_inv_id_apply]
            right_inv := fun b =>
              (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.apply_symm_apply (show B from b) }⟩

theorem finite_Bmod [IsFinite (Spec.map φ)] : Module.Finite A (Bmod φ) := by
  have h : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  exact h

theorem flat_Bmod [Flat (Spec.map φ)] : Module.Flat A (Bmod φ) := by
  have h : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  exact h

theorem finitePresentation_Bmod [IsFinite (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)] :
    Module.FinitePresentation A (Bmod φ) := by
  have h : φ.hom.FinitePresentation := (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  have : Algebra.FinitePresentation A (Bmod φ) := h
  have := finite_Bmod φ
  exact Module.FinitePresentation.of_finite_of_finitePresentation A (Bmod φ)

theorem finrank_Bmod [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] (n : ℕ)
    (hn : ∀ p : Spec A, (Spec.map φ).finrank p = n)
    (K : Type u) [Field K] [Algebra A K] : Module.finrank K (K ⊗[A] Bmod φ) = n := by
  have := finite_Bmod φ
  have := flat_Bmod φ
  let I : Ideal A := RingHom.ker (algebraMap A K)
  have hI : I.IsPrime := RingHom.ker_isPrime _
  have hrk : Module.rankAtStalk (R := A) (Bmod φ) ⟨I, hI⟩ = n := by
    have h1 := hn ⟨I, hI⟩
    rw [Scheme.Hom.finrank_SpecMap_eq_finrank ((IsFinite.SpecMap_iff φ).mp inferInstance)
      (Flat.SpecMap_iff.mp inferInstance)] at h1
    exact h1
  let ψ : I.ResidueField →+* K := Ideal.ResidueField.lift I (algebraMap A K) le_rfl (by
    intro a ha
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr (fun h0 => ha (by simpa [I, RingHom.mem_ker] using h0)))
  let : Algebra I.ResidueField K := ψ.toAlgebra
  have : IsScalarTower A I.ResidueField K := IsScalarTower.of_algebraMap_eq (fun a =>
    (Ideal.ResidueField.lift_algebraMap I (algebraMap A K) le_rfl _ a).symm)
  let e : K ⊗[A] Bmod φ ≃ₗ[K] K ⊗[I.ResidueField] (I.ResidueField ⊗[A] Bmod φ) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A I.ResidueField K K (Bmod φ)).symm
  rw [e.finrank_eq, Module.finrank_baseChange, Ideal.finrank_fiber_eq_rankAtStalk, hrk]

theorem core [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)]
    (n : ℕ) (hn : ∀ p : Spec A, (Spec.map φ).finrank p = n) :
    IsLocallyFreeOfRank n (M₀ φ) := by
  obtain ⟨e⟩ := exists_linearEquiv φ
  have := finite_Bmod φ
  have := flat_Bmod φ
  have := finitePresentation_Bmod φ
  have : Module.Projective A (Bmod φ) := Module.Flat.projective_of_finitePresentation
  have : Module.Finite A (P₀ φ) := Module.Finite.equiv e.symm
  have : Module.Projective A (P₀ φ) := Module.Projective.of_equiv e.symm
  have hP : IsLocallyFreeOfRank n (tilde (P₀ φ)) := by
    refine isLocallyFreeOfRank_tilde (P₀ φ) n fun K _ _ => ?_
    rw [← finrank_Bmod φ n hn K]
    exact LinearEquiv.finrank_eq (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e)
  have := isIso_fromTildeΓ φ
  exact IsLocallyFreeOfRank.of_iso (asIso (Scheme.Modules.fromTildeΓ (R := A) (M₀ φ))) hP

end affine

/-- Restrict the given module trivialization to a smaller open subset. -/
noncomputable def restrictTriv {Z : Scheme.{u}} {N : Z.Modules} {U₀ U : Z.Opens} (h : U ≤ U₀)
    (e : (Scheme.Modules.pullback U₀.ι).obj N ≅ 𝟙_ (U₀ : Scheme.{u}).Modules) :
    (Scheme.Modules.pullback U.ι).obj N ≅ 𝟙_ (U : Scheme.{u}).Modules :=
  (pullbackCongr (Z.homOfLE_ι h).symm).app N ≪≫
    ((pullbackComp (Z.homOfLE h) U₀.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (Z.homOfLE h)).mapIso e ≪≫
    pullbackTensorUnitObjIso (Z.homOfLE h)

theorem main {Z T : Scheme.{u}} (q : Z ⟶ T) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  (n : ℕ)
    (hn : ∀ t : T, q.finrank t = n) (N : Z.Modules)
    (hN : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅ 𝟙_ (↑(q ⁻¹ᵁ W) :
        Scheme.{u}).Modules)) :
    IsLocallyFreeOfRank n ((Scheme.Modules.pushforward q).obj N) := by
  refine isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback q N n fun y => ?_
  obtain ⟨W₀, hyW₀, ⟨e₀⟩⟩ := hN y
  obtain ⟨_, ⟨W, hWmem, rfl⟩, hyW, hWle⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hyW₀ W₀.isOpen
  have hW : IsAffineOpen W := hWmem
  have hW' : IsAffineOpen (q ⁻¹ᵁ W) := hW.preimage q
  let φ : Γ(T, W) ⟶ Γ(Z, q ⁻¹ᵁ W) := q.appLE W (q ⁻¹ᵁ W) le_rfl
  have hsq : IsPullback hW'.fromSpec (Spec.map φ) q hW.fromSpec :=
    (IsOpenImmersion.isPullback (Spec.map φ) hW'.fromSpec hW.fromSpec q
      (hW.SpecMap_appLE_fromSpec q hW' le_rfl).symm
      (by rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec])).flip
  refine ⟨W, hyW, Spec (Γ(T, W)), Spec (Γ(Z, q ⁻¹ᵁ W)), hW.isoSpec.symm, Spec.map φ, hW'.fromSpec,
    ?_, ?_⟩
  · simpa [IsAffineOpen.isoSpec_inv_ι] using hsq
  · have : IsFinite (Spec.map φ) := MorphismProperty.of_isPullback hsq inferInstance
    have : Flat (Spec.map φ) := MorphismProperty.of_isPullback hsq inferInstance
    have : LocallyOfFinitePresentation (Spec.map φ) := MorphismProperty.of_isPullback hsq
      inferInstance
    have hn' : ∀ p : Spec Γ(T, W), (Spec.map φ).finrank p = n := fun p => by
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq, hn]
    have eN : (Scheme.Modules.pullback hW'.fromSpec).obj N ≅ 𝟙_ (Spec Γ(Z, q ⁻¹ᵁ W)).Modules :=
      (pullbackCongr (show hW'.fromSpec = hW'.isoSpec.inv ≫ (q ⁻¹ᵁ W).ι from rfl)).app N ≪≫
        ((pullbackComp hW'.isoSpec.inv (q ⁻¹ᵁ W).ι).app N).symm ≪≫
        (Scheme.Modules.pullback hW'.isoSpec.inv).mapIso
          (restrictTriv (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ W₀ from fun z hz => hWle hz) e₀) ≪≫
        pullbackTensorUnitObjIso hW'.isoSpec.inv
    exact IsLocallyFreeOfRank.of_iso ((Scheme.Modules.pushforward (Spec.map φ)).mapIso eN.symm)
      (core φ n hn')

end Ws31X1

open Ws31X1 (main) in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.Modules
theorem isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
    {Z T : Scheme.{u}} (q : Z ⟶ T) [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] (n : ℕ)
    (hn : ∀ t : T, q.finrank t = n) (N : Z.Modules)
    (hN : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅ 𝟙_ (↑(q ⁻¹ᵁ W) :
        Scheme.{u}).Modules)) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward q).obj N) :=
  main q n hn N hN
end Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb) in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
attribute [-instance]
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
