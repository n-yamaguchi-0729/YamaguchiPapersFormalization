/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Command
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Adjoin.FG
import AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit
import AlgebraicCurves.Foundations.Algebra.Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit

/-!
# exists fg subalgebra is Pullback of is Affine of locally Of Finite Presentation
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace M1b3

variable {A₀ R A : Type u} [CommRing A₀] [CommRing R] [CommRing A] [Algebra A₀ R] [Algebra R A]
  [Algebra A₀ A]

/--
The finitely generated intermediate algebras containing the prescribed finite set and the
base-ring image.
-/
abbrev Idx (s : Finset A) : Type u :=
  {S : Subalgebra A₀ A // S.FG ∧ (↑s : Set A) ⊆ S ∧ Set.range (algebraMap R A) ⊆ S}
omit [Algebra A₀ R] in
theorem idx_directed (s : Finset A) (a b : Idx (A₀ := A₀) (R := R) s) : ∃ c : Idx (A₀ := A₀) (R :=
  R) s, a ≤ c ∧ b ≤ c :=
  ⟨⟨a.1 ⊔ b.1, a.2.1.sup b.2.1, a.2.2.1.trans (SetLike.coe_subset_coe.mpr le_sup_left),
    a.2.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩, (le_sup_left : a.1 ≤ a.1 ⊔ b.1),
    (le_sup_right : b.1 ≤ a.1 ⊔ b.1)⟩

scoped instance (s : Finset A) : IsDirected (Idx (A₀ := A₀) (R := R) s) (· ≤ ·) := ⟨idx_directed s⟩

scoped instance (s : Finset A) : IsDirectedOrder (Idx (A₀ := A₀) (R := R) s) := ⟨idx_directed s⟩

/-- The inclusion homomorphism between two finitely generated stages. -/
def stageMap (s : Finset A) (i j : Idx (A₀ := A₀) (R := R) s) (h : i ≤ j) : ↥i.1 →+* ↥j.1 :=
  (Subalgebra.inclusion h).toRingHom

scoped instance directedSystem (s : Finset A) :
    DirectedSystem (fun i : Idx (A₀ := A₀) (R := R) s => ↥i.1) (fun i j h => ⇑(stageMap s i j h))
      where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

omit [Algebra A₀ R] in
theorem isDirectLimit (s : Finset A) [Nonempty (Idx (A₀ := A₀) (R := R) s)] :
    IsDirectLimit (fun (i j : Idx (A₀ := A₀) (R := R) s) h => ⇑(stageMap s i j h)) (fun i =>
      ⇑(algebraMap (↥i.1) A)) := by
  classical
  refine ⟨fun a => ?_, fun i j mi mj h => ?_, fun _ _ _ _ => rfl⟩
  · obtain ⟨i⟩ := (inferInstance : Nonempty (Idx (A₀ := A₀) (R := R) s))
    have hfg : (Algebra.adjoin A₀ ({a} : Set A)).FG :=
      by simpa using Subalgebra.fg_adjoin_finset (R := A₀) {a}
    refine ⟨⟨i.1 ⊔ Algebra.adjoin A₀ {a}, i.2.1.sup hfg, i.2.2.1.trans (SetLike.coe_subset_coe.mpr
      le_sup_left),
      i.2.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩, ⟨a, ?_⟩, rfl⟩
    exact (le_sup_right : Algebra.adjoin A₀ {a} ≤ i.1 ⊔ Algebra.adjoin A₀ {a})
      (Algebra.self_mem_adjoin_singleton A₀ a)
  · obtain ⟨k, hik, hjk⟩ := idx_directed s i j
    exact ⟨k, hik, hjk, Subtype.ext h⟩

end M1b3

open Lean Elab Command in
run_cmd
  for word in ([
      ("AlgebraicCurves.Geometry.Schemes.Proofs." ++
        "exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation." ++
        "M1b3")
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


open M1b3 in
theorem m1_main
    {A₀ R A : Type u} [CommRing A₀] [CommRing R] [CommRing A] [Algebra A₀ R] [Algebra R A] [Algebra
      A₀ A]
    [IsScalarTower A₀ R A] [Algebra.FiniteType A₀ R]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation g]
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧ Set.range (algebraMap R A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsAffine X₀ ∧ LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
        IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by
  classical
  obtain ⟨genR, hgenR⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A₀ R).FG)
  let t₀ : Finset A := s ∪ genR.image (algebraMap R A)
  have hrange : Set.range (algebraMap R A) ⊆ Algebra.adjoin A₀ (↑t₀ : Set A) := by
    rintro _ ⟨r, rfl⟩
    have hr : r ∈ Algebra.adjoin A₀ (↑genR : Set R) := by rw [hgenR]; trivial
    have : (algebraMap R A) r = (IsScalarTower.toAlgHom A₀ R A) r := rfl
    rw [this]
    refine (Algebra.adjoin_le ?_ : Algebra.adjoin A₀ (↑genR : Set R) ≤
      (Algebra.adjoin A₀ (↑t₀ : Set A)).comap (IsScalarTower.toAlgHom A₀ R A)) hr
    intro x hx
    change (IsScalarTower.toAlgHom A₀ R A) x ∈ Algebra.adjoin A₀ (↑t₀ : Set A)
    apply Algebra.subset_adjoin
    apply Finset.mem_coe.mpr
    apply Finset.mem_union_right
    exact Finset.mem_image_of_mem _ hx
  have : Nonempty (Idx (A₀ := A₀) (R := R) s) :=
    ⟨⟨Algebra.adjoin A₀ (↑t₀ : Set A), Subalgebra.fg_adjoin_finset t₀,
      fun x hx => Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_left _ hx)), hrange⟩⟩
  let B : Type u := Γ(X, ⊤)
  let φ : A →+* B := g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hφ : RingHom.FinitePresentation φ := by
    have h1 : RingHom.FinitePresentation g.appTop.hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mp inferInstance
    exact RingHom.finitePresentation_respectsIso.2 g.appTop.hom
      (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv h1
  let algB : Algebra A B := φ.toAlgebra
  have : Algebra.FinitePresentation A B := hφ
  have hg : g = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    have h1 := Scheme.isoSpec_hom_naturality g
    rw [Scheme.isoSpec_Spec_hom] at h1
    have h2 : Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ Spec.map (Scheme.ΓSpecIso
      (CommRingCat.of A)).inv = 𝟙 _ := by
      rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
    calc g = g ≫ (Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ Spec.map (Scheme.ΓSpecIso
      (CommRingCat.of A)).inv) := by
          rw [h2, Category.comp_id]
      _ = (X.isoSpec.hom ≫ Spec.map g.appTop) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv
        := by
          rw [← Category.assoc, ← h1]
      _ = X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop) := by
          rw [Category.assoc, ← Spec.map_comp]
      _ = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
          rw [show CommRingCat.ofHom φ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop from by
            rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom]]
  obtain ⟨i, A', instCR, instAlg, instFP, ⟨e⟩⟩ :=
    Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
      (fun i : Idx (A₀ := A₀) (R := R) s => ↥i.1) (fun i j h => stageMap s i j h) A (isDirectLimit
        s) B
  let T : Subalgebra A₀ A := i.1
  let e' : CommRingCat.of (A ⊗[↥T] A') ≅ CommRingCat.of B := e.toRingEquiv.toCommRingCatIso
  let eS : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of (A ⊗[↥T] A')) := Scheme.Spec.mapIso e'.op
  have heS : eS.hom = Spec.map e'.hom := rfl
  let e₁ : Spec (CommRingCat.of (A ⊗[↥T] A')) ≅ X := (X.isoSpec ≪≫ eS).symm
  let inR := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ↥T) (A := A) (B :=
    A')).toRingHom
  let inL := CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ↥T) (A := A) (B :=
    A'))
  refine ⟨T, i.2.1, i.2.2.1, i.2.2.2, Spec (CommRingCat.of A'), Spec.map (CommRingCat.ofHom
    (algebraMap (↥T) A')),
    e₁.inv ≫ Spec.map inR, inferInstance, ?_, inferInstance, inferInstance, ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr instFP)
  · have hP := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct (↥T) A
      A')).flip
    refine hP.of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, hg]
      change Spec.map inL = (eS.inv ≫ X.isoSpec.inv) ≫ X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        φ)
      rw [Category.assoc, Iso.inv_hom_id_assoc]
      have : eS.inv = Spec.map e'.inv := rfl
      rw [this, ← Spec.map_comp]
      congr 1
      ext x
      change (Algebra.TensorProduct.includeLeftRingHom (R := ↥T) (A := A) (B := A')) x =
        e.toRingEquiv.symm (φ x)
      rw [RingEquiv.eq_symm_apply]
      change e (algebraMap A (A ⊗[↥T] A') x) = φ x
      rw [AlgEquiv.commutes]
      rfl

end exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation in
theorem exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
    {A₀ R A : Type u} [CommRing A₀] [CommRing R] [CommRing A] [Algebra A₀ R] [Algebra R A] [Algebra
      A₀ A]
    [IsScalarTower A₀ R A] [Algebra.FiniteType A₀ R]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation g]
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧ Set.range (algebraMap R A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsAffine X₀ ∧ LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
        IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) :=
  m1_main g s
end AlgebraicGeometry
end ProofImplementation

attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
attribute [-simp] IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply
