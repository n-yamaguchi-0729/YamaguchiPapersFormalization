/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Set
import AlgebraicCurves.Foundations.Algebra.Mathlib_Algebra_IsDirectLimit
import AlgebraicCurves.Foundations.Algebra.Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit

/-!
# Smooth exists fg subalgebra of smooth pullback snd
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_exists_fg_subalgebra_of_smooth_pullback_snd

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace SmoothDescGC7

section Stages

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]

/--
The finitely generated stages containing an intermediate algebra and a prescribed finite subset.
-/
abbrev Stage (A₁ : Subalgebra A₀ A) (s : Finset A) : Type u :=
  {T : Subalgebra A₀ A // T.FG ∧ A₁ ≤ T ∧ (↑s : Set A) ⊆ T}

namespace Stage

variable (A₁ : Subalgebra A₀ A) (s : Finset A)

scoped instance isDirectedOrder : IsDirectedOrder (Stage A₁ s) :=
  ⟨fun i j => ⟨⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, i.2.2.1.trans le_sup_left,
      i.2.2.2.trans (SetLike.coe_subset_coe.mpr le_sup_left)⟩,
    (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

theorem nonempty (hA₁ : A₁.FG) : Nonempty (Stage A₁ s) :=
  ⟨⟨A₁ ⊔ Algebra.adjoin A₀ ↑s, hA₁.sup (Subalgebra.fg_adjoin_finset s), le_sup_left,
    Algebra.subset_adjoin.trans (SetLike.coe_subset_coe.mpr le_sup_right)⟩⟩

scoped instance algebra (i : Stage A₁ s) : Algebra A₁ i.1 :=
  (Subalgebra.inclusion i.2.2.1).toRingHom.toAlgebra

scoped instance isScalarTower_top (i : Stage A₁ s) : IsScalarTower A₁ i.1 A :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance isScalarTower_bot (i : Stage A₁ s) : IsScalarTower A₀ A₁ i.1 :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The algebra inclusion between finitely generated stages over the fixed intermediate algebra. -/
def incl (i j : Stage A₁ s) (h : i ≤ j) : i.1 →ₐ[A₁] j.1 :=
  { (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom with commutes' := fun _ => rfl }

@[scoped simp] theorem incl_apply (i j : Stage A₁ s) (h : i ≤ j) (x : i.1) : (incl A₁ s i j h x :
  A) = x := rfl

scoped instance directedSystem :
    DirectedSystem (fun i : Stage A₁ s => ↥i.1) (fun i j h => ⇑(incl A₁ s i j h)) where
  map_self := by intros; rfl
  map_map := by intros; rfl

theorem isDirectLimit (hA₁ : A₁.FG) :
    IsDirectLimit (fun i j h => ⇑(incl A₁ s i j h)) (fun i : Stage A₁ s => ⇑(algebraMap i.1 A))
      where
  surj := fun m => by
    classical
    let T : Subalgebra A₀ A := A₁ ⊔ Algebra.adjoin A₀ (↑(insert m s) : Set A)
    have hle : Algebra.adjoin A₀ (↑(insert m s) : Set A) ≤ T := le_sup_right
    have hT : T.FG ∧ A₁ ≤ T ∧ (↑s : Set A) ⊆ T :=
      ⟨hA₁.sup (Subalgebra.fg_adjoin_finset (insert m s)), le_sup_left,
        fun x hx => hle (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx)))⟩
    have hm : m ∈ T := hle (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_insert_self m s)))
    exact ⟨⟨T, hT⟩, ⟨m, hm⟩, rfl⟩
  inj := fun i j mi mj h => by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨k, hik, hjk, Subtype.ext h⟩
  compatibility := fun _ _ _ _ => rfl

end Stage

attribute [local instance] Stage.isDirectedOrder
attribute [local instance] Stage.algebra
attribute [local instance] Stage.isScalarTower_top
attribute [local instance] Stage.isScalarTower_bot
attribute [local simp] Stage.incl_apply
attribute [local instance] Stage.directedSystem


theorem exists_fg_subalgebra_smooth_tensorProduct
    {B₀ : Type u} [CommRing B₀] [Algebra A₀ B₀]
    [Algebra.FinitePresentation A₀ B₀] [Algebra.Smooth A (A ⊗[A₀] B₀)] (s : Finset A) :
    ∃ T : Subalgebra A₀ A, T.FG ∧ (↑s : Set A) ⊆ T ∧ Algebra.Smooth T (T ⊗[A₀] B₀) := by
  classical
  obtain ⟨A₁, B₁, _, _, hA₁, hB₁, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg A₀ A (A ⊗[A₀] B₀)
  have := hB₁
  have : Nonempty (Stage A₁ s) := Stage.nonempty A₁ s hA₁
  let e' : A ⊗[A₁] (A₁ ⊗[A₀] B₀) ≃ₐ[A] A ⊗[A₁] B₁ :=
    (Algebra.TensorProduct.cancelBaseChange A₀ A₁ A A B₀).trans e
  obtain ⟨i, e₀, -⟩ :=
    Algebra.exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
      (↥A₁) (fun i : Stage A₁ s => ↥i.1) (Stage.incl A₁ s) A (Stage.isDirectLimit A₁ s hA₁)
      (↥A₁ ⊗[A₀] B₀) B₁ e'
  refine ⟨i.1, i.2.1, i.2.2.2, ?_⟩
  have : Algebra.Smooth i.1 (i.1 ⊗[A₁] (A₁ ⊗[A₀] B₀)) := .of_equiv e₀.symm
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange A₀ A₁ i.1 i.1 B₀)

end Stages

attribute [local instance] Stage.isDirectedOrder
attribute [local instance] Stage.algebra
attribute [local instance] Stage.isScalarTower_top
attribute [local instance] Stage.isScalarTower_bot
attribute [local simp] Stage.incl_apply
attribute [local instance] Stage.directedSystem


theorem smooth_pullback_snd_Spec_iff {A₀ B R : Type u} [CommRing A₀] [CommRing B] [CommRing R]
    [Algebra A₀ B] [Algebra A₀ R] :
    Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A₀ B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ R)))) ↔ Algebra.Smooth R (R ⊗[A₀] B) := by
  have : MorphismProperty.RespectsIso @Smooth.{u} := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Smooth.{u})]
    exact affineLocally_respectsIso RingHom.Smooth RingHom.Smooth.respectsIso
  rw [← RingHom.smooth_algebraMap, ← CommRingCat.hom_ofHom (algebraMap R (R ⊗[A₀] B)),
    ← HasRingHomProperty.Spec_iff (P := @Smooth), ← pullbackSpecIso_inv_fst' A₀ R B,
    MorphismProperty.cancel_left_of_respectsIso @Smooth, ← pullbackSymmetry_hom_comp_snd,
    MorphismProperty.cancel_left_of_respectsIso @Smooth]

theorem smooth_tensor_of_le {A₀ A B : Type u} [CommRing A₀] [CommRing A] [CommRing B]
    [Algebra A₀ A] [Algebra A₀ B] (T' T : Subalgebra A₀ A) (h : T' ≤ T)
    [Algebra.Smooth T' (T' ⊗[A₀] B)] : Algebra.Smooth T (T ⊗[A₀] B) := by
  let : Algebra T' T := (Subalgebra.inclusion h).toAlgebra
  have : IsScalarTower A₀ T' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.Smooth T (T ⊗[T'] (T' ⊗[A₀] B)) := inferInstance
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange A₀ T' T T B)

end SmoothDescGC7

attribute [local instance] SmoothDescGC7.Stage.isDirectedOrder
attribute [local instance] SmoothDescGC7.Stage.algebra
attribute [local instance] SmoothDescGC7.Stage.isScalarTower_top
attribute [local instance] SmoothDescGC7.Stage.isScalarTower_bot
attribute [local simp] SmoothDescGC7.Stage.incl_apply
attribute [local instance] SmoothDescGC7.Stage.directedSystem


open SmoothDescGC7 in
theorem _root_.AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f]
      [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) := by
  classical
  have : MorphismProperty.RespectsIso @Smooth.{u} := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Smooth.{u})]
    exact affineLocally_respectsIso RingHom.Smooth RingHom.Smooth.respectsIso
  have sourceLocal (P : MorphismProperty Scheme.{u})
      (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
      [HasRingHomProperty P Q] : IsZariskiLocalAtSource P := inferInstance
  have : IsZariskiLocalAtSource @Smooth.{u} := sourceLocal _ RingHom.Smooth
  set gA := Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) with hgA
  have : CompactSpace ↥X := by
    constructor
    rw [← Set.preimage_univ (f := f.base)]
    exact QuasiCompact.isCompact_preimage (f := f) _ isOpen_univ isCompact_univ
  let 𝒰₀ := X.affineCover.finiteSubcover
  let 𝒰 : X.OpenCover := 𝒰₀.copy 𝒰₀.I₀ (fun i => Spec Γ(𝒰₀.X i, ⊤)) (fun i => (𝒰₀.X i).isoSpec.inv
    ≫ 𝒰₀.f i)
    (Equiv.refl _) (fun i => (𝒰₀.X i).isoSpec.symm) (fun i => rfl)
  have : Fintype 𝒰.I₀ := show Fintype 𝒰₀.I₀ from inferInstance
  let B : 𝒰.I₀ → Type u := fun i => Γ(𝒰₀.X i, ⊤)
  let φ : ∀ i, CommRingCat.of A₀ ⟶ Γ(𝒰₀.X i, ⊤) := fun i => Spec.preimage (𝒰.f i ≫ f)
  let alg : ∀ i, Algebra A₀ (B i) := fun i => (φ i).hom.toAlgebra
  have hchart : ∀ i, 𝒰.f i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A₀ (B i))) := by
    intro i
    exact (Spec.map_preimage (𝒰.f i ≫ f)).symm
  have hfp : ∀ i, Algebra.FinitePresentation A₀ (B i) := by
    intro i
    have h1 : LocallyOfFinitePresentation (𝒰.f i ≫ f) := inferInstance
    rw [hchart] at h1
    exact RingHom.finitePresentation_algebraMap.mp ((HasRingHomProperty.Spec_iff (P :=
      @LocallyOfFinitePresentation)).mp h1)
  have hsmA : ∀ i, Algebra.Smooth A (A ⊗[A₀] B i) := by
    intro i
    rw [← smooth_pullback_snd_Spec_iff, ← hgA]
    have key : Smooth (pullback.snd (𝒰.f i ≫ f) gA) := by
      refine (MorphismProperty.cancel_left_of_respectsIso @Smooth (pullbackRightPullbackFstIso f gA
        (𝒰.f i)).hom _).mp ?_
      rw [pullbackRightPullbackFstIso_hom_snd]
      infer_instance
    exact (hchart i) ▸ key
  have hT : ∀ i, ∃ T : Subalgebra A₀ A, T.FG ∧ (↑s : Set A) ⊆ T ∧ Algebra.Smooth T (T ⊗[A₀] B i) :=
    fun i => exists_fg_subalgebra_smooth_tensorProduct (A₀ := A₀) (A := A) (B₀ := B i) s
  choose Ti hTi using hT
  have hgen : ∀ i, ∃ t : Finset A, Algebra.adjoin A₀ ↑t = Ti i := fun i => (hTi i).1
  choose t ht using hgen
  let T : Subalgebra A₀ A := Algebra.adjoin A₀ ↑(s ∪ Finset.univ.biUnion t)
  have hTfg : T.FG := Subalgebra.fg_adjoin_finset _
  have hsT : (↑s : Set A) ⊆ T := fun x hx => Algebra.subset_adjoin (Finset.mem_union_left _ hx)
  have hle : ∀ i, Ti i ≤ T := by
    intro i
    rw [← ht i]
    apply Algebra.adjoin_mono
    intro x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hx⟩)
  have hsmT : ∀ i, Algebra.Smooth T (T ⊗[A₀] B i) := fun i =>
    haveI := (hTi i).2.2
    smooth_tensor_of_le (Ti i) T (hle i)
  refine ⟨T, hTfg, hsT, ?_⟩
  set gT := Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)) with hgT
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (Scheme.Pullback.openCoverOfLeft 𝒰 f gT)
  change ∀ i : 𝒰.I₀, Smooth ((Scheme.Pullback.openCoverOfLeft 𝒰 f gT).f i ≫ pullback.snd f gT)
  intro i
  have h1 : (Scheme.Pullback.openCoverOfLeft 𝒰 f gT).f i ≫ pullback.snd f gT = pullback.snd (𝒰.f i
    ≫ f) gT := by
    erw [Scheme.Pullback.openCoverOfLeft_f]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have key : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A₀ (B i)))) gT) := by
    rw [hgT, smooth_pullback_snd_Spec_iff]; exact hsmT i
  rw [h1]
  change Smooth (pullback.snd (𝒰.f i ≫ f) gT)
  rw [hchart]
  exact key
end AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_exists_fg_subalgebra_of_smooth_pullback_snd
end ProofImplementation

attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
attribute [-simp] IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply
