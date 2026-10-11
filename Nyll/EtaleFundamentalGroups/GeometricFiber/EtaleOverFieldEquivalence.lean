/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Action.Continuous
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FiniteGaloisSets
public import Nyll.EtaleFundamentalGroups.ContinuousActions.FiniteOrbits
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ContinuousGaloisSet
public import Nyll.SchemeTheory.Etale.OverField.ConnectedSourceToCoproduct
public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Étale schemes over a field and discrete Galois sets

This file assembles the finite Galois equivalence orbit by orbit.  Its inverse
sends a discrete continuous Galois set to the coproduct of the finite étale
schemes corresponding to its finite orbits.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits MorphismProperty PreGaloisCategory
open scoped AlgebraicGeometry.FiniteEtale FintypeCatDiscrete

namespace AlgebraicGeometry.Scheme.Etale

private instance : IsZariskiLocalAtSource
    (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]

private abbrev G := K ≃ₐ[k] K

attribute [local instance] IsSepClosure.sep_closed

private noncomputable def orbitQuotientEquivOfEquivariant
    {H α β : Type u} [Group H] [MulAction H α] [MulAction H β]
    (e : α ≃ β) (he : ∀ (g : H) (x : α), e (g • x) = g • e x) :
    MulAction.orbitRel.Quotient H α ≃
      MulAction.orbitRel.Quotient H β :=
  Quotient.congr e (fun a b ↦ by
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, (he g b).symm.trans (congrArg e hg)⟩
    · rintro ⟨g, hg⟩
      refine ⟨g, e.injective ?_⟩
      exact (he g b).trans hg)

private noncomputable def orbitEquivOfEquivariant
    {H α β : Type u} [Group H] [MulAction H α] [MulAction H β]
    (e : α ≃ β) (he : ∀ (g : H) (x : α), e (g • x) = g • e x)
    (ω : MulAction.orbitRel.Quotient H α) :
    ω.orbit ≃ (orbitQuotientEquivOfEquivariant e he ω).orbit where
  toFun x := ⟨e x, by
    rw [MulAction.orbitRel.Quotient.mem_orbit]
    simpa only [orbitQuotientEquivOfEquivariant, Quotient.congr_mk] using
      congrArg (orbitQuotientEquivOfEquivariant e he)
        (MulAction.orbitRel.Quotient.mem_orbit.mp x.property)⟩
  invFun y := ⟨e.symm y, by
    rw [MulAction.orbitRel.Quotient.mem_orbit]
    apply (orbitQuotientEquivOfEquivariant e he).injective
    simpa only [orbitQuotientEquivOfEquivariant, Quotient.congr_mk,
      Equiv.apply_symm_apply] using
        MulAction.orbitRel.Quotient.mem_orbit.mp y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)

private lemma orbitEquivOfEquivariant_smul
    {H α β : Type u} [Group H] [MulAction H α] [MulAction H β]
    (e : α ≃ β) (he : ∀ (g : H) (x : α), e (g • x) = g • e x)
    (ω : MulAction.orbitRel.Quotient H α) (g : H) (x : ω.orbit) :
    orbitEquivOfEquivariant e he ω (g • x) =
      g • orbitEquivOfEquivariant e he ω x :=
  Subtype.ext (he g x)

private noncomputable def sigmaOrbitQuotientEquiv
    {H ι : Type u} [Group H] (A : ι → Type u)
    [∀ i, MulAction H (A i)] [∀ i, MulAction.IsPretransitive H (A i)]
    [∀ i, Nonempty (A i)] :
    MulAction.orbitRel.Quotient H (Σ i, A i) ≃ ι where
  toFun := Quotient.lift Sigma.fst (by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨g, h⟩
    simpa only [Sigma.smul_mk, Sigma.mk.injEq] using
      (congrArg Sigma.fst h).symm)
  invFun i := Quotient.mk'' ⟨i, Classical.arbitrary (A i)⟩
  left_inv ω := by
    induction ω using Quotient.inductionOn' with
    | _ x =>
      rcases x with ⟨i, x⟩
      rw [Quotient.eq'']
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H x
        (Classical.arbitrary (A i))
      refine ⟨g, ?_⟩
      exact Sigma.ext rfl (heq_of_eq hg)
  right_inv i := rfl

private noncomputable def sigmaOrbitEquivFiber
    {H ι : Type u} [Group H] (A : ι → Type u)
    [∀ i, MulAction H (A i)] [∀ i, MulAction.IsPretransitive H (A i)]
    [∀ i, Nonempty (A i)]
    (ω : MulAction.orbitRel.Quotient H (Σ i, A i)) :
    ω.orbit ≃ A (sigmaOrbitQuotientEquiv A ω) where
  toFun x := by
    let h : x.1.1 = sigmaOrbitQuotientEquiv A ω := by
      have hx := MulAction.orbitRel.Quotient.mem_orbit.mp x.property
      exact congrArg (sigmaOrbitQuotientEquiv A) hx
    exact h ▸ x.1.2
  invFun a := ⟨⟨sigmaOrbitQuotientEquiv A ω, a⟩, by
    rw [MulAction.orbitRel.Quotient.mem_orbit]
    apply (sigmaOrbitQuotientEquiv A).injective
    rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i, x⟩, hx⟩
    have hi : i = sigmaOrbitQuotientEquiv A ω := by
      exact congrArg (sigmaOrbitQuotientEquiv A)
        (MulAction.orbitRel.Quotient.mem_orbit.mp hx)
    subst i
    rfl
  right_inv a := rfl

private lemma sigmaOrbitEquivFiber_smul
    {H ι : Type u} [Group H] (A : ι → Type u)
    [∀ i, MulAction H (A i)] [∀ i, MulAction.IsPretransitive H (A i)]
    [∀ i, Nonempty (A i)]
    (ω : MulAction.orbitRel.Quotient H (Σ i, A i))
    (g : H) (x : ω.orbit) :
    sigmaOrbitEquivFiber A ω (g • x) =
      g • sigmaOrbitEquivFiber A ω x := by
  rcases x with ⟨⟨i, x⟩, hx⟩
  have hi : i = sigmaOrbitQuotientEquiv A ω := by
    exact congrArg (sigmaOrbitQuotientEquiv A)
      (MulAction.orbitRel.Quotient.mem_orbit.mp hx)
  subst i
  rfl

private noncomputable abbrev finiteEtaleComponent
    {ι : Type u} (L : ι → CommRingCat.{u})
    (a : ∀ i, CommRingCat.of k ⟶ L i)
    (hField : ∀ i, IsField (L i))
    (hFiniteSep : ∀ i, letI := (a i).hom.toAlgebra
      Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i))
    (i : ι) :
    AlgebraicGeometry.FiniteEtale (Spec (.of k)) := by
  letI : Field (L i) := (hField i).toField
  letI : Algebra k (L i) := (a i).hom.toAlgebra
  have hfs := hFiniteSep i
  letI : Module.Finite k (L i) := hfs.1
  letI : Algebra.IsSeparable k (L i) := hfs.2
  letI : Algebra.FormallyEtale k (L i) :=
    Algebra.FormallyEtale.of_isSeparable k (L i)
  letI : Module.FinitePresentation k (L i) :=
    Module.finitePresentation_of_finite k (L i)
  letI : Algebra.FinitePresentation k (L i) := inferInstance
  letI : Algebra.Etale k (L i) :=
    { formallyEtale := inferInstance
      finitePresentation := inferInstance }
  letI : Algebra.FiniteEtale k (L i) := ⟨⟩
  letI : IsFiniteEtale (Spec.map (a i)) := by
    rw [IsFiniteEtale.SpecMap_iff]
    change Algebra.FiniteEtale k (L i)
    infer_instance
  exact AlgebraicGeometry.FiniteEtale.mk (Spec.map (a i))

@[simp]
private lemma finiteEtaleComponent_hom
    {ι : Type u} (L : ι → CommRingCat.{u})
    (a : ∀ i, CommRingCat.of k ⟶ L i)
    (hField : ∀ i, IsField (L i))
    (hFiniteSep : ∀ i, letI := (a i).hom.toAlgebra
      Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i))
    (i : ι) :
    (finiteEtaleComponent k L a hField hFiniteSep i).hom = Spec.map (a i) :=
  rfl

include K in
private theorem finiteEtaleComponent_isConnected
    {ι : Type u} (L : ι → CommRingCat.{u})
    (a : ∀ i, CommRingCat.of k ⟶ L i)
    (hField : ∀ i, IsField (L i))
    (hFiniteSep : ∀ i, letI := (a i).hom.toAlgebra
      Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i))
    (i : ι) :
    PreGaloisCategory.IsConnected
      (finiteEtaleComponent k L a hField hFiniteSep i) := by
  let : Field (L i) := (hField i).toField
  let : Algebra k (L i) := (a i).hom.toAlgebra
  have hfs := hFiniteSep i
  let : Module.Finite k (L i) := hfs.1
  let : Algebra.IsSeparable k (L i) := hfs.2
  let : Algebra.FormallyEtale k (L i) :=
    Algebra.FormallyEtale.of_isSeparable k (L i)
  let : Module.FinitePresentation k (L i) :=
    Module.finitePresentation_of_finite k (L i)
  let : Algebra.FinitePresentation k (L i) := inferInstance
  let : Algebra.Etale k (L i) :=
    { formallyEtale := inferInstance
      finitePresentation := inferInstance }
  let : Algebra.FiniteEtale k (L i) := ⟨⟩
  let : IsFiniteEtale (Spec.map (a i)) := by
    rw [IsFiniteEtale.SpecMap_iff]
    change Algebra.FiniteEtale k (L i)
    infer_instance
  change PreGaloisCategory.IsConnected
    (AlgebraicGeometry.FiniteEtale.mk (Spec.map (a i)))
  let Z := AlgebraicGeometry.FiniteEtale.mk (Spec.map (a i))
  constructor
  · apply (not_initial_iff_fiber_nonempty (fib k K) Z).mpr
    let φ : L i →ₐ[k] K := IsSepClosed.lift
    let x : Over.mk (ξ k K) ⟶ Z.toComma :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
        change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Z.hom = ξ k K
        have hZhom : Z.hom = Spec.map (a i) := rfl
        have hring :
            a i ≫ CommRingCat.ofHom φ.toRingHom =
              CommRingCat.ofHom (algebraMap k K) := by
          ext z
          exact φ.commutes z
        rw [hZhom]
        exact (Spec.map_comp (a i)
          (CommRingCat.ofHom φ.toRingHom)).symm.trans
            (congrArg Spec.map hring))
    exact ⟨(AlgebraicGeometry.FiniteEtale.fiberObjEquivHom
      (ξ k K) Z).symm x⟩
  · intro Y j _ hj
    have hjOpen :
        IsOpenImmersion j.left :=
      ((AlgebraicGeometry.FiniteEtale.mono_iff (Spec (.of k)) Y Z j).mp
        (inferInstance : Mono j)).1
    let : IsOpenImmersion j.left := hjOpen
    have hFY :
        Nonempty ((fib k K).obj Y) :=
      (not_initial_iff_fiber_nonempty
        (fib k K) Y).mp hj
    let : Nonempty Y.left :=
      hFY.map AlgebraicGeometry.FiniteEtale.fiberPt
    let : Subsingleton Z.left := by
      change Subsingleton (PrimeSpectrum (L i))
      rw [PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
      exact hField i
    have hjSurjective : Function.Surjective j.left := by
      intro z
      let y : Y.left := Classical.arbitrary Y.left
      exact ⟨y, Subsingleton.elim _ _⟩
    have hjRange : j.left.opensRange = ⊤ := by
      apply TopologicalSpace.Opens.ext
      rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top]
      exact Set.range_eq_univ.mpr hjSurjective
    let : IsIso j.left :=
      isIso_of_isOpenImmersion_of_opensRange_eq_top j.left hjRange
    exact AlgebraicGeometry.FiniteEtale.isIso_of_isIso_left j

omit [IsSepClosure k K] in
private lemma sigmaOverHom_ext
    {ι : Type u} (Z : ι → Over (Spec (.of k)))
    {q r : Σ i, (Over.mk (ξ k K) ⟶ Z i)}
    (h :
      (⟨q.1, q.2.left⟩ :
          Σ i, (Over.mk (ξ k K)).left ⟶ (Z i).left) =
        (⟨r.1, r.2.left⟩ :
          Σ i, (Over.mk (ξ k K)).left ⟶ (Z i).left)) :
    q = r := by
  rcases q with ⟨i, q⟩
  rcases r with ⟨j, r⟩
  have hidx := (Sigma.ext_iff.mp h).1
  cases hidx
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply CategoryTheory.Over.OverMorphism.ext
  exact eq_of_heq (Sigma.ext_iff.mp h).2

private noncomputable def geometricFiberDecompositionEquiv
    {ι : Type u} (X : (Spec (.of k)).Etale)
    (Z : ι → AlgebraicGeometry.FiniteEtale (Spec (.of k)))
    (e : (∐ fun i ↦ (Z i).left) ≅ X.left)
    (he : e.hom ≫ X.hom = Sigma.desc (fun i ↦ (Z i).hom)) :
    (Over.mk (ξ k K) ⟶ X.toComma) ≃
      Σ i, (Over.mk (ξ k K) ⟶ (Z i).toComma) where
  toFun x := by
    let q := Scheme.homSigmaEquiv (fun i ↦ (Z i).left)
      (Spec (.of K)) (x.left ≫ e.inv)
    refine ⟨q.1, Over.homMk q.2 ?_⟩
    change q.2 ≫ (Z q.1).hom = ξ k K
    have hq : q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1 =
        x.left ≫ e.inv := by
      dsimp only [q]
      rw [← Scheme.homSigmaEquiv_symm_apply]
      exact (Scheme.homSigmaEquiv (fun i ↦ (Z i).left)
        (Spec (.of K))).symm_apply_apply (x.left ≫ e.inv)
    have hx : x.left =
        (q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ e.hom := by
      calc
        x.left = x.left ≫ (e.inv ≫ e.hom) := by
          rw [e.inv_hom_id, Category.comp_id]
        _ = (x.left ≫ e.inv) ≫ e.hom := (Category.assoc _ _ _).symm
        _ = (q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ e.hom :=
          congrArg (fun m ↦ m ≫ e.hom) hq.symm
    let D : (∐ fun i ↦ (Z i).left) ⟶ Spec (.of k) :=
      Sigma.desc (fun i ↦ (Z i).hom)
    have hι :
        Sigma.ι (fun i ↦ (Z i).left) q.1 ≫ D = (Z q.1).hom :=
      Sigma.ι_comp_desc (fun i ↦ (Z i).hom) q.1
    have h1 :
        q.2 ≫ (Z q.1).hom =
          q.2 ≫ (Sigma.ι (fun i ↦ (Z i).left) q.1 ≫ D) :=
      congrArg (fun m ↦ q.2 ≫ m) hι.symm
    have h2 :
        q.2 ≫ (Sigma.ι (fun i ↦ (Z i).left) q.1 ≫ D) =
          (q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ D :=
      (Category.assoc _ _ _).symm
    have h3 :
        (q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ D =
          (q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫
            (e.hom ≫ X.hom) :=
      congrArg
        (fun m ↦
          (q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ m)
        he.symm
    have h4 :
        (q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫
            (e.hom ≫ X.hom) =
          ((q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ e.hom) ≫
            X.hom :=
      (Category.assoc _ _ _).symm
    have h5 :
        ((q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ e.hom) ≫
            X.hom =
          x.left ≫ X.hom :=
      congrArg (fun m ↦ m ≫ X.hom) hx.symm
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans x.w))))
  invFun q := Over.homMk
    ((q.2.left ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ e.hom) (by
      change ((q.2.left ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ e.hom) ≫
        X.hom = ξ k K
      let D : (∐ fun i ↦ (Z i).left) ⟶ Spec (.of k) :=
        Sigma.desc (fun i ↦ (Z i).hom)
      have hι :
          Sigma.ι (fun i ↦ (Z i).left) q.1 ≫ D = (Z q.1).hom :=
        Sigma.ι_comp_desc (fun i ↦ (Z i).hom) q.1
      have h1 :
          ((q.2.left ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ e.hom) ≫
              X.hom =
            (q.2.left ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫
              (e.hom ≫ X.hom) :=
        Category.assoc _ _ _
      have h2 :
          (q.2.left ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫
              (e.hom ≫ X.hom) =
            (q.2.left ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ D :=
        congrArg
          (fun m ↦
            (q.2.left ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ m) he
      have h3 :
          (q.2.left ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ D =
            q.2.left ≫
              (Sigma.ι (fun i ↦ (Z i).left) q.1 ≫ D) :=
        Category.assoc _ _ _
      have h4 :
          q.2.left ≫
              (Sigma.ι (fun i ↦ (Z i).left) q.1 ≫ D) =
            q.2.left ≫ (Z q.1).hom :=
        congrArg (fun m ↦ q.2.left ≫ m) hι
      exact h1.trans (h2.trans (h3.trans (h4.trans q.2.w))))
  left_inv x := by
    dsimp only
    apply CategoryTheory.Over.OverMorphism.ext
    let q := Scheme.homSigmaEquiv (fun i ↦ (Z i).left)
      (Spec (.of K)) (x.left ≫ e.inv)
    have hq : q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1 =
        x.left ≫ e.inv := by
      dsimp only [q]
      rw [← Scheme.homSigmaEquiv_symm_apply]
      exact (Scheme.homSigmaEquiv (fun i ↦ (Z i).left)
        (Spec (.of K))).symm_apply_apply (x.left ≫ e.inv)
    calc
      (q.2 ≫ Sigma.ι (fun i ↦ (Z i).left) q.1) ≫ e.hom =
          (x.left ≫ e.inv) ≫ e.hom :=
        congrArg (fun m ↦ m ≫ e.hom) hq
      _ = x.left ≫ (e.inv ≫ e.hom) := Category.assoc _ _ _
      _ = x.left ≫ 𝟙 _ :=
        congrArg (fun m ↦ x.left ≫ m) e.inv_hom_id
      _ = x.left := Category.comp_id _
  right_inv q := by
    rcases q with ⟨i, y⟩
    let E := Scheme.homSigmaEquiv (fun j ↦ (Z j).left) (Spec (.of K))
    change
      (⟨(E ((((y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) ≫
          e.hom) ≫ e.inv))).1,
        CategoryTheory.Over.homMk
          (E ((((y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) ≫
            e.hom) ≫ e.inv))).2 _⟩ :
        Σ j, (Over.mk (ξ k K) ⟶ (Z j).toComma)) =
      (⟨i, y⟩ : Σ j, (Over.mk (ξ k K) ⟶ (Z j).toComma))
    have hs : (((y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) ≫
        e.hom) ≫ e.inv) =
        y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i := by
      calc
        _ = (y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) ≫
              (e.hom ≫ e.inv) := Category.assoc _ _ _
        _ = (y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) ≫ 𝟙 _ :=
          congrArg (fun m ↦
            (y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) ≫ m)
            e.hom_inv_id
        _ = _ := Category.comp_id _
    have hr :
        E ((((y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) ≫
          e.hom) ≫ e.inv)) = ⟨i, y.left⟩ := by
      calc
        E ((((y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) ≫
            e.hom) ≫ e.inv)) =
            E (y.left ≫ Sigma.ι (fun j ↦ (Z j).left) i) :=
          congrArg E hs
        _ = ⟨i, y.left⟩ := by
          have h := E.apply_symm_apply ⟨i, y.left⟩
          rw [Scheme.homSigmaEquiv_symm_apply] at h
          exact h
    apply sigmaOverHom_ext k K (fun j ↦ (Z j).toComma)
    exact hr

omit [IsSepClosure k K] in
private lemma geometricFiberDecompositionEquiv_rho
    {ι : Type u} (X : (Spec (.of k)).Etale)
    (Z : ι → AlgebraicGeometry.FiniteEtale (Spec (.of k)))
    (e : (∐ fun i ↦ (Z i).left) ≅ X.left)
    (he : e.hom ≫ X.hom = Sigma.desc (fun i ↦ (Z i).hom))
    (g : G k K) (x : Over.mk (ξ k K) ⟶ X.toComma) :
    geometricFiberDecompositionEquiv k K X Z e he
        (ConcreteCategory.hom
          (((geometricFiber k K).obj X).obj.obj.ρ g) x) =
      g • geometricFiberDecompositionEquiv k K X Z e he x := by
  let σ : Spec (.of K) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (g : K →+* K))
  let q := Scheme.homSigmaEquiv (fun i ↦ (Z i).left)
    (Spec (.of K)) (x.left ≫ e.inv)
  let xg : Over.mk (ξ k K) ⟶ X.toComma :=
    ConcreteCategory.hom
      (((geometricFiber k K).obj X).obj.obj.ρ g) x
  let qg := Scheme.homSigmaEquiv (fun i ↦ (Z i).left)
    (Spec (.of K)) (xg.left ≫ e.inv)
  have hxg : xg.left ≫ e.inv = σ ≫ (x.left ≫ e.inv) := by
    change
      (Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ x.left) ≫ e.inv =
        σ ≫ (x.left ≫ e.inv)
    dsimp only [σ]
    exact Category.assoc _ _ _
  have hqg : qg = ⟨q.1, σ ≫ q.2⟩ := by
    dsimp only [qg, q]
    calc
      Scheme.homSigmaEquiv (fun i ↦ (Z i).left) (Spec (.of K))
          (xg.left ≫ e.inv) =
          Scheme.homSigmaEquiv (fun i ↦ (Z i).left) (Spec (.of K))
            (σ ≫ (x.left ≫ e.inv)) :=
        congrArg
          (Scheme.homSigmaEquiv (fun i ↦ (Z i).left) (Spec (.of K))) hxg
      _ = ⟨(Scheme.homSigmaEquiv (fun i ↦ (Z i).left)
              (Spec (.of K)) (x.left ≫ e.inv)).1,
            σ ≫ (Scheme.homSigmaEquiv (fun i ↦ (Z i).left)
              (Spec (.of K)) (x.left ≫ e.inv)).2⟩ :=
        Scheme.homSigmaEquiv_comp (fun i ↦ (Z i).left)
          σ (x.left ≫ e.inv)
  apply sigmaOverHom_ext k K (fun i ↦ (Z i).toComma)
  change qg = ⟨q.1, σ ≫ q.2⟩
  exact hqg

/-- The map on orbit sets induced by an equivariant map. -/
private def orbitIndexMap
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T) :
    MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) →
      MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj T) :=
  Quotient.map'
    (fun x : (forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S ↦
      f.hom.hom.hom x) (by
    rintro a b ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    exact (ConcreteCategory.congr_hom (f.hom.hom.comm g) b).symm)

/-- Restriction of an equivariant map to one source orbit. -/
private def orbitMap
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T)
    (ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
    ω.orbit → (orbitIndexMap k K f ω).orbit := fun x ↦
  ⟨f.hom.hom.hom x.1, by
    have hx : Quotient.mk'' x.1 = ω :=
      (MulAction.orbitRel.Quotient.mem_orbit).1 x.property
    have hmap : Quotient.mk'' (f.hom.hom.hom x.1) =
        orbitIndexMap k K f (Quotient.mk'' x.1) := rfl
    exact (MulAction.orbitRel.Quotient.mem_orbit).2
      (hmap.trans (congrArg (orbitIndexMap k K f) hx))⟩

/-- Restriction of an equivariant map to one source orbit, bundled as a
morphism of finite continuous actions. -/
private noncomputable def orbitContActionMap
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T)
    (ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
    DiscreteContAction.orbitContAction S ω ⟶
      DiscreteContAction.orbitContAction T (orbitIndexMap k K f ω) :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (orbitMap k K f ω)
      comm := fun g ↦ by
        ext x
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (f.hom.hom.comm g) x.1 }

/-- The finite étale scheme corresponding to one orbit. -/
private noncomputable abbrev orbitFiniteEtale
    (S : DiscreteContAction TopCat (G k K))
    (ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
    AlgebraicGeometry.FiniteEtale (Spec (.of k)) :=
  (AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.obj
    (DiscreteContAction.orbitContAction S ω)

/-- The finite étale morphism corresponding to the restriction of an
equivariant map to one orbit. -/
private noncomputable abbrev orbitFiniteEtaleMap
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T)
    (ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
    orbitFiniteEtale k K S ω ⟶
      orbitFiniteEtale k K T (orbitIndexMap k K f ω) :=
  (AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.map
    (orbitContActionMap k K f ω)

/-- Object part of the inverse in Tag `03QR`: take the coproduct of the
finite étale schemes attached to all orbits. -/
private noncomputable abbrev inverseObj
    (S : DiscreteContAction TopCat (G k K)) :
    (Spec (.of k)).Etale := by
  let d : (∐ fun ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
      (orbitFiniteEtale k K S ω).left) ⟶ Spec (.of k) :=
    Sigma.desc (fun ω ↦ (orbitFiniteEtale k K S ω).hom)
  haveI : AlgebraicGeometry.Etale d :=
    IsZariskiLocalAtSource.sigmaDesc (fun ω ↦
      (inferInstance :
        IsFiniteEtale (orbitFiniteEtale k K S ω).hom).toEtale)
  exact Scheme.Etale.mk d

@[simp]
private lemma inverseObj_hom
    (S : DiscreteContAction TopCat (G k K)) :
    (inverseObj k K S).hom =
      Sigma.desc (fun ω : MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
        (orbitFiniteEtale k K S ω).hom) :=
  rfl

/-- Morphism part of the inverse: each source orbit is sent into the orbit
containing its image, then the finite Galois equivalence is applied. -/
private noncomputable abbrev inverseMap
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T) :
    inverseObj k K S ⟶ inverseObj k K T := by
  let YS := fun ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
    (orbitFiniteEtale k K S ω).left
  let YT := fun η : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj T) ↦
    (orbitFiniteEtale k K T η).left
  let hS := fun ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
    (orbitFiniteEtale k K S ω).hom
  let hT := fun η : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj T) ↦
    (orbitFiniteEtale k K T η).hom
  let d : (∐ YS) ⟶ (∐ YT) :=
    Sigma.desc (fun ω ↦
      (orbitFiniteEtaleMap k K f ω).left ≫
        Sigma.ι YT (orbitIndexMap k K f ω))
  have hd : d ≫ Sigma.desc hT = Sigma.desc hS := by
    apply Sigma.hom_ext
    intro ω
    have hιd : Sigma.ι YS ω ≫ d =
        (orbitFiniteEtaleMap k K f ω).left ≫
          Sigma.ι YT (orbitIndexMap k K f ω) := by
      dsimp only [d]
      exact Sigma.ι_comp_desc _ ω
    have hιT : Sigma.ι YT (orbitIndexMap k K f ω) ≫
        Sigma.desc hT =
        (orbitFiniteEtale k K T (orbitIndexMap k K f ω)).hom :=
      Sigma.ι_comp_desc hT _
    have hιS : Sigma.ι YS ω ≫ Sigma.desc hS =
        (orbitFiniteEtale k K S ω).hom := Sigma.ι_comp_desc hS ω
    have h1 :
        Sigma.ι YS ω ≫ (d ≫ Sigma.desc hT) =
          (Sigma.ι YS ω ≫ d) ≫ Sigma.desc hT :=
      (Category.assoc _ _ _).symm
    have h2 :
        (Sigma.ι YS ω ≫ d) ≫ Sigma.desc hT =
          ((orbitFiniteEtaleMap k K f ω).left ≫
            Sigma.ι YT (orbitIndexMap k K f ω)) ≫ Sigma.desc hT :=
      congrArg (fun t ↦ t ≫ Sigma.desc hT) hιd
    have h3 :
        ((orbitFiniteEtaleMap k K f ω).left ≫
            Sigma.ι YT (orbitIndexMap k K f ω)) ≫ Sigma.desc hT =
          (orbitFiniteEtaleMap k K f ω).left ≫
            (Sigma.ι YT (orbitIndexMap k K f ω) ≫ Sigma.desc hT) :=
      Category.assoc _ _ _
    have h4 :
        (orbitFiniteEtaleMap k K f ω).left ≫
            (Sigma.ι YT (orbitIndexMap k K f ω) ≫ Sigma.desc hT) =
          (orbitFiniteEtaleMap k K f ω).left ≫
            (orbitFiniteEtale k K T (orbitIndexMap k K f ω)).hom :=
      congrArg (fun t ↦ (orbitFiniteEtaleMap k K f ω).left ≫ t) hιT
    have h5 :
        (orbitFiniteEtaleMap k K f ω).left ≫
            (orbitFiniteEtale k K T (orbitIndexMap k K f ω)).hom =
          (orbitFiniteEtale k K S ω).hom :=
      MorphismProperty.Over.w (orbitFiniteEtaleMap k K f ω)
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans hιS.symm))))
  exact MorphismProperty.Over.homMk d hd

@[simp]
private lemma inverseMap_left
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T) :
    (inverseMap k K f).left =
      Sigma.desc (fun ω ↦
        (orbitFiniteEtaleMap k K f ω).left ≫
          Sigma.ι
            (fun η : MulAction.orbitRel.Quotient (G k K)
                ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj T) ↦
              (orbitFiniteEtale k K T η).left)
            (orbitIndexMap k K f ω)) :=
  rfl

/-- The orbitwise-coproduct inverse functor. -/
private noncomputable abbrev inverseFunctor :
    DiscreteContAction TopCat (G k K) ⥤ (Spec (.of k)).Etale where
  obj := inverseObj k K
  map := inverseMap k K
  map_id S := by
    apply MorphismProperty.Over.Hom.ext
    apply Sigma.hom_ext
    intro ω
    induction ω using Quotient.inductionOn'
    rename_i a
    let Y := fun η : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
      (orbitFiniteEtale k K S η).left
    have hι :
        Sigma.ι Y (Quotient.mk'' a) ≫ (inverseMap k K (𝟙 S)).left =
          (orbitFiniteEtaleMap k K (𝟙 S) (Quotient.mk'' a)).left ≫
            Sigma.ι Y (Quotient.mk'' a) := by
      rw [inverseMap_left]
      exact Sigma.ι_comp_desc _ _
    have hm : orbitContActionMap k K (𝟙 S) (Quotient.mk'' a) = 𝟙 _ := by
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      ext x
      rfl
    have hf :
        orbitFiniteEtaleMap k K (𝟙 S) (Quotient.mk'' a) = 𝟙 _ := by
      change
        (AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.map
            (orbitContActionMap k K (𝟙 S) (Quotient.mk'' a)) =
          𝟙 _
      rw [hm]
      exact CategoryTheory.Functor.map_id _ _
    rw [hf] at hι
    have hidSource :
        (𝟙 (orbitFiniteEtale k K S (Quotient.mk'' a)) :
          orbitFiniteEtale k K S (Quotient.mk'' a) ⟶
            orbitFiniteEtale k K S (Quotient.mk'' a)).left = 𝟙 _ := rfl
    have hidTarget :
        (𝟙 (inverseObj k K S) :
          inverseObj k K S ⟶ inverseObj k K S).left = 𝟙 _ := rfl
    have hsource :
        (𝟙 (orbitFiniteEtale k K S (Quotient.mk'' a)) :
            orbitFiniteEtale k K S (Quotient.mk'' a) ⟶
              orbitFiniteEtale k K S (Quotient.mk'' a)).left ≫
            Sigma.ι Y (Quotient.mk'' a) =
          Sigma.ι Y (Quotient.mk'' a) := by
      calc
        _ = 𝟙 _ ≫ Sigma.ι Y (Quotient.mk'' a) :=
          congrArg (fun t ↦ t ≫ Sigma.ι Y (Quotient.mk'' a)) hidSource
        _ = _ := Category.id_comp _
    have htarget :
        Sigma.ι Y (Quotient.mk'' a) ≫
            (𝟙 (inverseObj k K S) :
              inverseObj k K S ⟶ inverseObj k K S).left =
          Sigma.ι Y (Quotient.mk'' a) := by
      calc
        _ = Sigma.ι Y (Quotient.mk'' a) ≫ 𝟙 _ :=
          congrArg (fun t ↦ Sigma.ι Y (Quotient.mk'' a) ≫ t) hidTarget
        _ = _ := Category.comp_id _
    exact hι.trans (hsource.trans htarget.symm)
  map_comp f g := by
    rename_i S T U
    apply MorphismProperty.Over.Hom.ext
    apply Sigma.hom_ext
    intro ω
    induction ω using Quotient.inductionOn'
    rename_i a
    let YS := fun η : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
      (orbitFiniteEtale k K S η).left
    let YT := fun η : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj T) ↦
      (orbitFiniteEtale k K T η).left
    let YU := fun η : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj U) ↦
      (orbitFiniteEtale k K U η).left
    have hιf :
        Sigma.ι YS (Quotient.mk'' a) ≫ (inverseMap k K f).left =
          (orbitFiniteEtaleMap k K f (Quotient.mk'' a)).left ≫
            Sigma.ι YT (orbitIndexMap k K f (Quotient.mk'' a)) := by
      rw [inverseMap_left]
      exact Sigma.ι_comp_desc _ _
    have hιg :
        Sigma.ι YT (orbitIndexMap k K f (Quotient.mk'' a)) ≫
            (inverseMap k K g).left =
          (orbitFiniteEtaleMap k K g
              (orbitIndexMap k K f (Quotient.mk'' a))).left ≫
            Sigma.ι YU
              (orbitIndexMap k K g
                (orbitIndexMap k K f (Quotient.mk'' a))) := by
      rw [inverseMap_left]
      exact Sigma.ι_comp_desc _ _
    have hιfg :
        Sigma.ι YS (Quotient.mk'' a) ≫ (inverseMap k K (f ≫ g)).left =
          (orbitFiniteEtaleMap k K (f ≫ g) (Quotient.mk'' a)).left ≫
            Sigma.ι YU
              (orbitIndexMap k K (f ≫ g) (Quotient.mk'' a)) := by
      rw [inverseMap_left]
      exact Sigma.ι_comp_desc _ _
    have hm :
        orbitContActionMap k K (f ≫ g) (Quotient.mk'' a) =
          orbitContActionMap k K f (Quotient.mk'' a) ≫
            orbitContActionMap k K g
              (orbitIndexMap k K f (Quotient.mk'' a)) := by
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      ext x
      rfl
    have hf :
        orbitFiniteEtaleMap k K (f ≫ g) (Quotient.mk'' a) =
          orbitFiniteEtaleMap k K f (Quotient.mk'' a) ≫
            orbitFiniteEtaleMap k K g
              (orbitIndexMap k K f (Quotient.mk'' a)) := by
      change
        (AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.map
            (orbitContActionMap k K (f ≫ g) (Quotient.mk'' a)) =
          (AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.map
              (orbitContActionMap k K f (Quotient.mk'' a)) ≫
            (AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.map
              (orbitContActionMap k K g
                (orbitIndexMap k K f (Quotient.mk'' a)))
      rw [hm]
      exact CategoryTheory.Functor.map_comp _ _ _
    have hright :
        Sigma.ι YS (Quotient.mk'' a) ≫
            ((inverseMap k K f).left ≫ (inverseMap k K g).left) =
          ((orbitFiniteEtaleMap k K f (Quotient.mk'' a)).left ≫
            (orbitFiniteEtaleMap k K g
              (orbitIndexMap k K f (Quotient.mk'' a))).left) ≫
            Sigma.ι YU
              (orbitIndexMap k K g
                (orbitIndexMap k K f (Quotient.mk'' a))) := by
      calc
        _ = (Sigma.ι YS (Quotient.mk'' a) ≫
              (inverseMap k K f).left) ≫ (inverseMap k K g).left :=
            (Category.assoc _ _ _).symm
        _ = ((orbitFiniteEtaleMap k K f (Quotient.mk'' a)).left ≫
              Sigma.ι YT (orbitIndexMap k K f (Quotient.mk'' a))) ≫
              (inverseMap k K g).left :=
            congrArg (fun t ↦ t ≫ (inverseMap k K g).left) hιf
        _ = _ := by
            let u := (orbitFiniteEtaleMap k K f (Quotient.mk'' a)).left
            let v := Sigma.ι YT (orbitIndexMap k K f (Quotient.mk'' a))
            let w := (inverseMap k K g).left
            let z := (orbitFiniteEtaleMap k K g
              (orbitIndexMap k K f (Quotient.mk'' a))).left
            let j := Sigma.ι YU
              (orbitIndexMap k K g
                (orbitIndexMap k K f (Quotient.mk'' a)))
            have h₁ : (u ≫ v) ≫ w = u ≫ (v ≫ w) := Category.assoc _ _ _
            have h₂ : u ≫ (v ≫ w) = u ≫ (z ≫ j) :=
              congrArg (fun t ↦ u ≫ t) hιg
            have h₃ : u ≫ (z ≫ j) = (u ≫ z) ≫ j :=
              (Category.assoc _ _ _).symm
            exact h₁.trans (h₂.trans h₃)
    rw [hf] at hιfg
    change
      Sigma.ι YS (Quotient.mk'' a) ≫ (inverseMap k K (f ≫ g)).left =
        Sigma.ι YS (Quotient.mk'' a) ≫
          ((inverseMap k K f).left ≫ (inverseMap k K g).left)
    simpa only [MorphismProperty.Comma.comp_left] using hιfg.trans hright.symm

/-- A geometric point of the coproduct defining `inverseObj` is uniquely a
geometric point of one orbit summand. -/
private noncomputable def inverseObjGeometricFiberEquiv
    (S : DiscreteContAction TopCat (G k K)) :
    (Over.mk (ξ k K) ⟶ (inverseObj k K S).toComma) ≃
      Σ ω : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S),
        (Over.mk (ξ k K) ⟶ (orbitFiniteEtale k K S ω).toComma) where
  toFun x := by
    let q := Scheme.homSigmaEquiv
      (fun ω : MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
        (orbitFiniteEtale k K S ω).left) (Spec (.of K)) x.left
    refine ⟨q.1, Over.homMk q.2 ?_⟩
    change q.2 ≫ (orbitFiniteEtale k K S q.1).hom = ξ k K
    have hx := x.w
    change x.left ≫ Sigma.desc
      (fun ω : MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
        (orbitFiniteEtale k K S ω).hom) = ξ k K at hx
    have hq : q.2 ≫ Sigma.ι
        (fun ω : MulAction.orbitRel.Quotient (G k K)
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
          (orbitFiniteEtale k K S ω).left) q.1 = x.left := by
      simpa only [q, Scheme.homSigmaEquiv_symm_apply] using
        (Scheme.homSigmaEquiv
          (fun ω : MulAction.orbitRel.Quotient (G k K)
              ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
            (orbitFiniteEtale k K S ω).left)
          (Spec (.of K))).symm_apply_apply x.left
    let D :
        (∐ fun ω : MulAction.orbitRel.Quotient (G k K)
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
          (orbitFiniteEtale k K S ω).left) ⟶ Spec (.of k) :=
      Sigma.desc
        (fun ω : MulAction.orbitRel.Quotient (G k K)
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
          (orbitFiniteEtale k K S ω).hom)
    have hι :
        Sigma.ι
            (fun ω : MulAction.orbitRel.Quotient (G k K)
                ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
              (orbitFiniteEtale k K S ω).left) q.1 ≫ D =
          (orbitFiniteEtale k K S q.1).hom :=
      Sigma.ι_comp_desc
        (fun ω : MulAction.orbitRel.Quotient (G k K)
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
          (orbitFiniteEtale k K S ω).hom) q.1
    have h1 :
        q.2 ≫ (orbitFiniteEtale k K S q.1).hom =
          q.2 ≫
            (Sigma.ι
                (fun ω : MulAction.orbitRel.Quotient (G k K)
                    ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
                  (orbitFiniteEtale k K S ω).left) q.1 ≫ D) :=
      congrArg (fun m ↦ q.2 ≫ m) hι.symm
    have h2 :
        q.2 ≫
            (Sigma.ι
                (fun ω : MulAction.orbitRel.Quotient (G k K)
                    ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
                  (orbitFiniteEtale k K S ω).left) q.1 ≫ D) =
          (q.2 ≫ Sigma.ι
            (fun ω : MulAction.orbitRel.Quotient (G k K)
                ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
              (orbitFiniteEtale k K S ω).left) q.1) ≫ D :=
      (Category.assoc _ _ _).symm
    have h3 :
        (q.2 ≫ Sigma.ι
            (fun ω : MulAction.orbitRel.Quotient (G k K)
                ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
              (orbitFiniteEtale k K S ω).left) q.1) ≫ D =
          x.left ≫ D :=
      congrArg (fun m ↦ m ≫ D) hq
    exact h1.trans (h2.trans (h3.trans hx))
  invFun q := Over.homMk
    (q.2.left ≫ Sigma.ι
      (fun ω : MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
        (orbitFiniteEtale k K S ω).left) q.1) (by
      change (q.2.left ≫ Sigma.ι
        (fun ω : MulAction.orbitRel.Quotient (G k K)
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
          (orbitFiniteEtale k K S ω).left) q.1) ≫
        Sigma.desc
          (fun ω : MulAction.orbitRel.Quotient (G k K)
              ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
            (orbitFiniteEtale k K S ω).hom) = ξ k K
      let D :
          (∐ fun ω : MulAction.orbitRel.Quotient (G k K)
              ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
            (orbitFiniteEtale k K S ω).left) ⟶ Spec (.of k) :=
        Sigma.desc
          (fun ω : MulAction.orbitRel.Quotient (G k K)
              ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
            (orbitFiniteEtale k K S ω).hom)
      have hι :
          Sigma.ι
              (fun ω : MulAction.orbitRel.Quotient (G k K)
                  ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
                (orbitFiniteEtale k K S ω).left) q.1 ≫ D =
            (orbitFiniteEtale k K S q.1).hom :=
        Sigma.ι_comp_desc
          (fun ω : MulAction.orbitRel.Quotient (G k K)
              ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
            (orbitFiniteEtale k K S ω).hom) q.1
      have h1 :
          (q.2.left ≫ Sigma.ι
            (fun ω : MulAction.orbitRel.Quotient (G k K)
                ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
              (orbitFiniteEtale k K S ω).left) q.1) ≫ D =
            q.2.left ≫
              (Sigma.ι
                (fun ω : MulAction.orbitRel.Quotient (G k K)
                    ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
                  (orbitFiniteEtale k K S ω).left) q.1 ≫ D) :=
        Category.assoc _ _ _
      have h2 :
          q.2.left ≫
              (Sigma.ι
                (fun ω : MulAction.orbitRel.Quotient (G k K)
                    ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
                  (orbitFiniteEtale k K S ω).left) q.1 ≫ D) =
            q.2.left ≫ (orbitFiniteEtale k K S q.1).hom :=
        congrArg (fun m ↦ q.2.left ≫ m) hι
      exact h1.trans (h2.trans q.2.w))
  left_inv x := by
    dsimp only
    apply CategoryTheory.Over.OverMorphism.ext
    let q := Scheme.homSigmaEquiv
      (fun ω : MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
        (orbitFiniteEtale k K S ω).left) (Spec (.of K)) x.left
    change q.2 ≫ Sigma.ι
      (fun ω : MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
        (orbitFiniteEtale k K S ω).left) q.1 = x.left
    simpa only [q, Scheme.homSigmaEquiv_symm_apply] using
      (Scheme.homSigmaEquiv
        (fun ω : MulAction.orbitRel.Quotient (G k K)
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
          (orbitFiniteEtale k K S ω).left)
        (Spec (.of K))).symm_apply_apply x.left
  right_inv q := by
    rcases q with ⟨ω, y⟩
    let Y := fun η : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
      (orbitFiniteEtale k K S η).left
    let E := Scheme.homSigmaEquiv Y (Spec (.of K))
    change
      (⟨(E (y.left ≫ Sigma.ι Y ω)).1,
        CategoryTheory.Over.homMk (E (y.left ≫ Sigma.ι Y ω)).2 _⟩ :
        Σ η : MulAction.orbitRel.Quotient (G k K)
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S),
          (Over.mk (ξ k K) ⟶ (orbitFiniteEtale k K S η).toComma)) =
      (⟨ω, y⟩ :
        Σ η : MulAction.orbitRel.Quotient (G k K)
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S),
          (Over.mk (ξ k K) ⟶ (orbitFiniteEtale k K S η).toComma))
    have hr : E (y.left ≫ Sigma.ι Y ω) = ⟨ω, y.left⟩ := by
      have h := E.apply_symm_apply ⟨ω, y.left⟩
      rw [Scheme.homSigmaEquiv_symm_apply] at h
      exact h
    apply sigmaOverHom_ext k K
      (fun η ↦ (orbitFiniteEtale k K S η).toComma)
    exact hr

/-- The underlying bijection supplied by the counit of the finite Galois
equivalence. -/
private noncomputable def finiteCounitEquiv
    (A : ContAction FintypeCat (G k K)) :
    (forget₂ (ContAction FintypeCat (G k K)) FintypeCat).obj
        ((AlgebraicGeometry.FiniteEtale.equivContAction k K).functor.obj
          ((AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.obj A)) ≃
      (forget₂ (ContAction FintypeCat (G k K)) FintypeCat).obj A :=
  FintypeCat.equivEquivIso.symm
    ((forget₂ (ContAction FintypeCat (G k K)) FintypeCat).mapIso
      ((AlgebraicGeometry.FiniteEtale.equivContAction k K).counitIso.app A))

/-- On a finite orbit, the finite Galois equivalence identifies the geometric
fiber of the corresponding finite étale scheme with that orbit. -/
private noncomputable def finiteGeometricFiberEquiv
    (A : ContAction FintypeCat (G k K)) :
    (Over.mk (ξ k K) ⟶
      ((AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.obj A).toComma) ≃
      (forget₂ (ContAction FintypeCat (G k K)) FintypeCat).obj A :=
  (AlgebraicGeometry.FiniteEtale.fiberObjEquivHom (ξ k K)
    ((AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.obj A)).symm.trans
      (finiteCounitEquiv k K A)

private lemma finiteGeometricFiberEquiv_smul
    (A : ContAction FintypeCat (G k K)) (g : G k K)
    (x : Over.mk (ξ k K) ⟶
      ((AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.obj A).toComma) :
    finiteGeometricFiberEquiv k K A (g • x) =
      ConcreteCategory.hom (A.obj.ρ g)
        (finiteGeometricFiberEquiv k K A x) := by
  let E := AlgebraicGeometry.FiniteEtale.equivContAction k K
  let Y := E.inverse.obj A
  let e := AlgebraicGeometry.FiniteEtale.fiberObjEquivHom (ξ k K) Y
  let z := e.symm x
  have hz : e.symm (g • x) = g • z := by
    symm
    simpa only [z, e, Equiv.apply_symm_apply] using
      (AlgebraicGeometry.FiniteEtale.algEquiv_smul_fiber_def
        k K Y g z)
  change finiteCounitEquiv k K A (e.symm (g • x)) =
    ConcreteCategory.hom (A.obj.ρ g)
      (finiteCounitEquiv k K A (e.symm x))
  rw [hz]
  have hc := ConcreteCategory.congr_hom
    ((E.counitIso.app A).hom.hom.comm g) z
  change finiteCounitEquiv k K A (g • z) =
    ConcreteCategory.hom (A.obj.ρ g)
      (finiteCounitEquiv k K A z) at hc
  exact hc

private lemma finiteGeometricFiberEquiv_naturality
    {A B : ContAction FintypeCat (G k K)} (f : A ⟶ B)
    (x : Over.mk (ξ k K) ⟶
      ((AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.obj A).toComma) :
    finiteGeometricFiberEquiv k K B
        (x ≫ ((AlgebraicGeometry.FiniteEtale.equivContAction k K).inverse.map f).hom) =
      f.hom.hom (finiteGeometricFiberEquiv k K A x) := by
  let E := AlgebraicGeometry.FiniteEtale.equivContAction k K
  let z := (AlgebraicGeometry.FiniteEtale.fiberObjEquivHom (ξ k K)
    (E.inverse.obj A)).symm x
  change finiteCounitEquiv k K B
      ((AlgebraicGeometry.FiniteEtale.fiberObjEquivHom (ξ k K)
        (E.inverse.obj B)).symm (x ≫ (E.inverse.map f).hom)) =
    f.hom.hom (finiteCounitEquiv k K A z)
  rw [← AlgebraicGeometry.FiniteEtale.fiberObjEquivHom_symm_naturality]
  have h := congrArg (fun q ↦ q.hom.hom)
    (E.counitIso.hom.naturality f)
  exact ConcreteCategory.congr_hom h z

/-- The objectwise counit bijection: split a geometric point by its unique
orbit summand, use the finite counit on that summand, then reassemble the
orbits. -/
private noncomputable def inverseObjCounitEquiv
    (S : DiscreteContAction TopCat (G k K)) :
    (Over.mk (ξ k K) ⟶ (inverseObj k K S).toComma) ≃
      (forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S :=
  (inverseObjGeometricFiberEquiv k K S).trans <|
    (Equiv.sigmaCongrRight (fun ω ↦
      finiteGeometricFiberEquiv k K
        (DiscreteContAction.orbitContAction S ω))).trans <|
      (MulAction.selfEquivSigmaOrbits' (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)).symm

private lemma inverseObjGeometricFiberEquiv_rho
    (S : DiscreteContAction TopCat (G k K)) (g : G k K)
    (x : Over.mk (ξ k K) ⟶ (inverseObj k K S).toComma) :
    inverseObjGeometricFiberEquiv k K S
        (ConcreteCategory.hom
          (((geometricFiber k K).obj (inverseObj k K S)).obj.obj.ρ g) x) =
      ⟨(inverseObjGeometricFiberEquiv k K S x).1,
        g • (inverseObjGeometricFiberEquiv k K S x).2⟩ := by
  let Y := fun ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
    (orbitFiniteEtale k K S ω).left
  let σ : Spec (.of K) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (g : K →+* K))
  let q := Scheme.homSigmaEquiv Y (Spec (.of K)) x.left
  let xg : Over.mk (ξ k K) ⟶ (inverseObj k K S).toComma :=
    ConcreteCategory.hom
      (((geometricFiber k K).obj (inverseObj k K S)).obj.obj.ρ g) x
  let qg := Scheme.homSigmaEquiv Y (Spec (.of K)) xg.left
  have hxg : xg.left = σ ≫ x.left := by
    change Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ x.left =
      σ ≫ x.left
    rfl
  have hqg : qg = ⟨q.1, σ ≫ q.2⟩ := by
    change Scheme.homSigmaEquiv Y (Spec (.of K)) xg.left =
      ⟨(Scheme.homSigmaEquiv Y (Spec (.of K)) x.left).1,
        σ ≫ (Scheme.homSigmaEquiv Y (Spec (.of K)) x.left).2⟩
    calc
      Scheme.homSigmaEquiv Y (Spec (.of K)) xg.left =
          Scheme.homSigmaEquiv Y (Spec (.of K)) (σ ≫ x.left) :=
        congrArg (Scheme.homSigmaEquiv Y (Spec (.of K))) hxg
      _ = ⟨(Scheme.homSigmaEquiv Y (Spec (.of K)) x.left).1,
            σ ≫ (Scheme.homSigmaEquiv Y (Spec (.of K)) x.left).2⟩ :=
        Scheme.homSigmaEquiv_comp Y σ x.left
  apply sigmaOverHom_ext k K
    (fun ω ↦ (orbitFiniteEtale k K S ω).toComma)
  change qg = ⟨q.1, σ ≫ q.2⟩
  exact hqg

private lemma inverseObjGeometricFiberEquiv_map
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T)
    (x : Over.mk (ξ k K) ⟶ (inverseObj k K S).toComma) :
    inverseObjGeometricFiberEquiv k K T
        ((geometricFiber k K).map (inverseMap k K f) x) =
      ⟨orbitIndexMap k K f (inverseObjGeometricFiberEquiv k K S x).1,
        (inverseObjGeometricFiberEquiv k K S x).2 ≫
          (orbitFiniteEtaleMap k K f
            (inverseObjGeometricFiberEquiv k K S x).1).hom⟩ := by
  let YS := fun ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
    (orbitFiniteEtale k K S ω).left
  let YT := fun η : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj T) ↦
    (orbitFiniteEtale k K T η).left
  let q := Scheme.homSigmaEquiv YS (Spec (.of K)) x.left
  let m := orbitFiniteEtaleMap k K f q.1
  let xm : Over.mk (ξ k K) ⟶ (inverseObj k K T).toComma :=
    (geometricFiber k K).map (inverseMap k K f) x
  let qm := Scheme.homSigmaEquiv YT (Spec (.of K)) xm.left
  have hx : x.left = q.2 ≫ Sigma.ι YS q.1 := by
    dsimp only [q]
    rw [← Scheme.homSigmaEquiv_symm_apply]
    exact (Scheme.homSigmaEquiv YS
      (Spec (.of K))).symm_apply_apply x.left |>.symm
  have hmleft :
      Sigma.ι YS q.1 ≫ (inverseMap k K f).left =
        m.left ≫ Sigma.ι YT (orbitIndexMap k K f q.1) := by
    change Sigma.ι YS q.1 ≫
        Sigma.desc (fun ω ↦
          (orbitFiniteEtaleMap k K f ω).left ≫
            Sigma.ι YT (orbitIndexMap k K f ω)) = _
    exact Sigma.ι_comp_desc
      (fun ω ↦ (orbitFiniteEtaleMap k K f ω).left ≫
        Sigma.ι YT (orbitIndexMap k K f ω)) q.1
  have hxm : xm.left =
      (q.2 ≫ m.left) ≫ Sigma.ι YT (orbitIndexMap k K f q.1) := by
    change x.left ≫ (inverseMap k K f).left = _
    rw [hx]
    have h₁ :
        (q.2 ≫ Sigma.ι YS q.1) ≫ (inverseMap k K f).left =
          q.2 ≫ (Sigma.ι YS q.1 ≫ (inverseMap k K f).left) :=
      Category.assoc _ _ _
    have h₂ :
        q.2 ≫ (Sigma.ι YS q.1 ≫ (inverseMap k K f).left) =
          q.2 ≫ (m.left ≫ Sigma.ι YT (orbitIndexMap k K f q.1)) :=
      congrArg (fun t ↦ q.2 ≫ t) hmleft
    have h₃ :
        q.2 ≫ (m.left ≫ Sigma.ι YT (orbitIndexMap k K f q.1)) =
          (q.2 ≫ m.left) ≫ Sigma.ι YT (orbitIndexMap k K f q.1) :=
      (Category.assoc _ _ _).symm
    exact h₁.trans (h₂.trans h₃)
  have hqm : qm =
      ⟨orbitIndexMap k K f q.1, q.2 ≫ m.left⟩ := by
    have h := (Scheme.homSigmaEquiv YT (Spec (.of K))).apply_symm_apply
      ⟨orbitIndexMap k K f q.1, q.2 ≫ m.left⟩
    rw [Scheme.homSigmaEquiv_symm_apply] at h
    rw [← hxm] at h
    exact h
  apply sigmaOverHom_ext k K
    (fun η ↦ (orbitFiniteEtale k K T η).toComma)
  change qm = ⟨orbitIndexMap k K f q.1, q.2 ≫ m.left⟩
  exact hqm

private lemma inverseObjCounitEquiv_rho
    (S : DiscreteContAction TopCat (G k K)) (g : G k K)
    (x : Over.mk (ξ k K) ⟶ (inverseObj k K S).toComma) :
    inverseObjCounitEquiv k K S
        (ConcreteCategory.hom
          (((geometricFiber k K).obj (inverseObj k K S)).obj.obj.ρ g) x) =
      g • inverseObjCounitEquiv k K S x := by
  let q := inverseObjGeometricFiberEquiv k K S x
  let E := Equiv.sigmaCongrRight (fun ω ↦
    finiteGeometricFiberEquiv k K
      (DiscreteContAction.orbitContAction S ω))
  let R := (MulAction.selfEquivSigmaOrbits' (G k K)
    ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)).symm
  have hq : inverseObjGeometricFiberEquiv k K S
      (ConcreteCategory.hom
        (((geometricFiber k K).obj (inverseObj k K S)).obj.obj.ρ g) x) =
      ⟨q.1, g • q.2⟩ :=
    inverseObjGeometricFiberEquiv_rho k K S g x
  have hf := finiteGeometricFiberEquiv_smul k K
    (DiscreteContAction.orbitContAction S q.1) g q.2
  change R (E (inverseObjGeometricFiberEquiv k K S
      (ConcreteCategory.hom
        (((geometricFiber k K).obj (inverseObj k K S)).obj.obj.ρ g) x))) =
    g • R (E q)
  calc
    _ = R (E ⟨q.1, g • q.2⟩) := congrArg (fun z ↦ R (E z)) hq
    _ = R ⟨q.1, ConcreteCategory.hom
          ((DiscreteContAction.orbitContAction S q.1).obj.ρ g)
          (finiteGeometricFiberEquiv k K
            (DiscreteContAction.orbitContAction S q.1) q.2)⟩ := by
      apply congrArg R
      exact Sigma.ext rfl (heq_of_eq hf)
    _ = g • R (E q) := rfl

private lemma inverseObjCounitEquiv_naturality
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T)
    (x : Over.mk (ξ k K) ⟶ (inverseObj k K S).toComma) :
    inverseObjCounitEquiv k K T
        ((geometricFiber k K).map (inverseMap k K f) x) =
      f.hom.hom.hom (inverseObjCounitEquiv k K S x) := by
  let q := inverseObjGeometricFiberEquiv k K S x
  let ES := Equiv.sigmaCongrRight (fun ω ↦
    finiteGeometricFiberEquiv k K
      (DiscreteContAction.orbitContAction S ω))
  let ET := Equiv.sigmaCongrRight (fun η ↦
    finiteGeometricFiberEquiv k K
      (DiscreteContAction.orbitContAction T η))
  let RS := (MulAction.selfEquivSigmaOrbits' (G k K)
    ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)).symm
  let RT := (MulAction.selfEquivSigmaOrbits' (G k K)
    ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj T)).symm
  have hq : inverseObjGeometricFiberEquiv k K T
      ((geometricFiber k K).map (inverseMap k K f) x) =
      ⟨orbitIndexMap k K f q.1,
        q.2 ≫ (orbitFiniteEtaleMap k K f q.1).hom⟩ :=
    inverseObjGeometricFiberEquiv_map k K f x
  have hf := finiteGeometricFiberEquiv_naturality k K
    (orbitContActionMap k K f q.1) q.2
  change RT (ET (inverseObjGeometricFiberEquiv k K T
      ((geometricFiber k K).map (inverseMap k K f) x))) =
    f.hom.hom.hom (RS (ES q))
  change RT (ET (inverseObjGeometricFiberEquiv k K T
      ((geometricFiber k K).map (inverseMap k K f) x))) =
    RT ⟨orbitIndexMap k K f q.1,
      (orbitContActionMap k K f q.1).hom.hom
        (finiteGeometricFiberEquiv k K
          (DiscreteContAction.orbitContAction S q.1) q.2)⟩
  rw [hq]
  apply congrArg RT
  exact Sigma.ext rfl (heq_of_eq hf)

/-- The objectwise counit is an isomorphism of discrete continuous actions. -/
private noncomputable def inverseObjCounitIso
    (S : DiscreteContAction TopCat (G k K)) :
    (geometricFiber k K).obj (inverseObj k K S) ≅ S := by
  let e := inverseObjCounitEquiv k K S
  let h :
      (forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj
          ((geometricFiber k K).obj (inverseObj k K S)) ≃ₜ
      (forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S :=
    { __ := e
      continuous_toFun := by
        let : DiscreteTopology
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj
              ((geometricFiber k K).obj (inverseObj k K S))) :=
          ((geometricFiber k K).obj (inverseObj k K S)).property
        exact continuous_of_discreteTopology
      continuous_invFun := by
        let : DiscreteTopology
            ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) := S.property
        exact continuous_of_discreteTopology }
  let a : ((geometricFiber k K).obj (inverseObj k K S)).obj.obj ≅ S.obj.obj :=
    Action.mkIso (TopCat.isoOfHomeo h) (fun g ↦ by
      ext x
      exact inverseObjCounitEquiv_rho k K S g x)
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ a)

/-- The orbitwise inverse followed by the geometric-fiber functor is
naturally isomorphic to the identity. -/
private noncomputable def inverseCounitIso :
    inverseFunctor k K ⋙ geometricFiber k K ≅
      𝟭 (DiscreteContAction TopCat (G k K)) :=
  NatIso.ofComponents (inverseObjCounitIso k K) (fun f ↦ by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    ext x
    exact inverseObjCounitEquiv_naturality k K f x)

/-- Before imposing naturality, the component decomposition of an étale
scheme identifies it with the orbitwise inverse of its geometric fiber. -/
private noncomputable def uncorrectedUnitObjIso
    (X : (Spec (.of k)).Etale) :
    inverseObj k K ((geometricFiber k K).obj X) ≅ X := by
  choose L a e hField hFiniteSep he using exists_iso_sigmaSpec k X
  let Z (i : X.left) : AlgebraicGeometry.FiniteEtale (Spec (.of k)) :=
    finiteEtaleComponent k L a hField hFiniteSep i
  letI connectedZ (i : X.left) : PreGaloisCategory.IsConnected (Z i) :=
    finiteEtaleComponent_isConnected k K L a hField hFiniteSep i
  let A (i : X.left) :=
    Over.mk (ξ k K) ⟶ (Z i).toComma
  letI nonemptyA (i : X.left) : Nonempty (A i) :=
    (nonempty_fiber_of_isConnected
      (fib k K) (Z i)).map
        (AlgebraicGeometry.FiniteEtale.fiberObjEquivHom (ξ k K) (Z i))
  letI pretransitiveA (i : X.left) :
      MulAction.IsPretransitive (G k K) (A i) := by
    constructor
    intro x y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G k K)
      ((AlgebraicGeometry.FiniteEtale.fiberObjEquivHom
        (ξ k K) (Z i)).symm x)
      ((AlgebraicGeometry.FiniteEtale.fiberObjEquivHom
        (ξ k K) (Z i)).symm y)
    refine ⟨g, ?_⟩
    apply (AlgebraicGeometry.FiniteEtale.fiberObjEquivHom
      (ξ k K) (Z i)).symm.injective
    simpa only [AlgebraicGeometry.FiniteEtale.algEquiv_smul_fiber_def,
      Equiv.apply_symm_apply] using hg
  have heZ :
      e.hom ≫ X.hom = Sigma.desc (fun i ↦ (Z i).hom) := by
    exact he
  let S := (geometricFiber k K).obj X
  let d :
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ≃
        Σ i, A i :=
    geometricFiberDecompositionEquiv k K X Z e heZ
  have hd (g : G k K)
      (x : (forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) :
      d (g • x) = g • d x := by
    exact geometricFiberDecompositionEquiv_rho k K X Z e heZ g x
  let q :
      MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ≃
        MulAction.orbitRel.Quotient (G k K) (Σ i, A i) :=
    orbitQuotientEquivOfEquivariant d hd
  let indexEquiv :
      MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ≃
        X.left :=
    q.trans (sigmaOrbitQuotientEquiv A)
  let rawOrbitEquiv
      (ω : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
      ω.orbit ≃ A (indexEquiv ω) :=
    (orbitEquivOfEquivariant d hd ω).trans
      (sigmaOrbitEquivFiber A (q ω))
  have rawOrbitEquiv_smul
      (ω : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S))
      (g : G k K) (x : ω.orbit) :
      rawOrbitEquiv ω (g • x) = g • rawOrbitEquiv ω x := by
    change sigmaOrbitEquivFiber A (q ω)
        (orbitEquivOfEquivariant d hd ω (g • x)) =
      g • sigmaOrbitEquivFiber A (q ω)
        (orbitEquivOfEquivariant d hd ω x)
    rw [orbitEquivOfEquivariant_smul, sigmaOrbitEquivFiber_smul]
  let fiberOrbitEquiv
      (ω : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
      ω.orbit ≃
        (fib k K).obj (Z (indexEquiv ω)) :=
    (rawOrbitEquiv ω).trans
      (AlgebraicGeometry.FiniteEtale.fiberObjEquivHom
        (ξ k K) (Z (indexEquiv ω))).symm
  have fiberOrbitEquiv_smul
      (ω : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S))
      (g : G k K) (x : ω.orbit) :
      fiberOrbitEquiv ω (g • x) = g • fiberOrbitEquiv ω x := by
    dsimp only [fiberOrbitEquiv, Equiv.trans_apply]
    rw [rawOrbitEquiv_smul]
    let y := rawOrbitEquiv ω x
    simpa only [y, Equiv.apply_symm_apply] using
      (AlgebraicGeometry.FiniteEtale.algEquiv_smul_fiber_def
        k K (Z (indexEquiv ω)) g
          ((AlgebraicGeometry.FiniteEtale.fiberObjEquivHom
            (ξ k K) (Z (indexEquiv ω))).symm y)).symm
  let E := AlgebraicGeometry.FiniteEtale.equivContAction k K
  let actionIso
      (ω : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
      DiscreteContAction.orbitContAction S ω ≅
        E.functor.obj (Z (indexEquiv ω)) := by
    refine ObjectProperty.isoMk _ ?_
    exact Action.mkIso
      (FintypeCat.equivEquivIso (fiberOrbitEquiv ω))
      (fun g ↦ by
        ext x
        exact fiberOrbitEquiv_smul ω g x)
  let componentIso
      (ω : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
      orbitFiniteEtale k K S ω ≅ Z (indexEquiv ω) :=
    E.inverse.mapIso (actionIso ω) ≪≫
      (E.unitIso.app (Z (indexEquiv ω))).symm
  let componentSchemeIso
      (ω : MulAction.orbitRel.Quotient (G k K)
        ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S)) :
      (orbitFiniteEtale k K S ω).left ≅ (Z (indexEquiv ω)).left :=
    (AlgebraicGeometry.FiniteEtale.forget (Spec (.of k)) ⋙
      Over.forget (Spec (.of k))).mapIso (componentIso ω)
  let componentSchemeIsoComp :
      ∀ ω : MulAction.orbitRel.Quotient (G k K)
          ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S),
        (orbitFiniteEtale k K S ω).left ≅
          ((fun i ↦ (Z i).left) ∘ indexEquiv) ω :=
    componentSchemeIso
  let YS := fun ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
    (orbitFiniteEtale k K S ω).left
  let hS := fun ω : MulAction.orbitRel.Quotient (G k K)
      ((forget₂ (DiscreteContAction TopCat (G k K)) TopCat).obj S) ↦
    (orbitFiniteEtale k K S ω).hom
  let totalIso : (∐ YS) ≅ X.left :=
    Sigma.mapIso componentSchemeIsoComp ≪≫
      Sigma.reindex indexEquiv (fun i ↦ (Z i).left) ≪≫ e
  have htotal : totalIso.hom ≫ X.hom = Sigma.desc hS := by
    apply Sigma.hom_ext
    intro ω
    have hιS : Sigma.ι YS ω ≫ Sigma.desc hS =
        (orbitFiniteEtale k K S ω).hom :=
      Sigma.ι_comp_desc hS ω
    have hmid :
        Sigma.ι YS ω ≫ (totalIso.hom ≫ X.hom) =
          (componentSchemeIso ω).hom ≫
            Sigma.ι (fun i ↦ (Z i).left) (indexEquiv ω) ≫
              e.hom ≫ X.hom := by
      calc
        _ = (Sigma.ι YS ω ≫ totalIso.hom) ≫ X.hom :=
          (Category.assoc _ _ _).symm
        _ = (componentSchemeIsoComp ω).hom ≫
            Sigma.ι ((fun i ↦ (Z i).left) ∘ indexEquiv) ω ≫
              (Sigma.reindex indexEquiv (fun i ↦ (Z i).left)).hom ≫
              e.hom ≫ X.hom := by
          simp only [totalIso, Iso.trans_hom, Category.assoc,
            Sigma.ι_mapIso_hom_assoc]
          have htrans :
              ((Sigma.reindex indexEquiv (fun i ↦ (Z i).left)) ≪≫ e).hom =
                (Sigma.reindex indexEquiv (fun i ↦ (Z i).left)).hom ≫ e.hom :=
            Iso.trans_hom _ _
          rw [htrans]
          exact congrArg
            (fun t ↦ (componentSchemeIsoComp ω).hom ≫
              Sigma.ι ((fun i ↦ (Z i).left) ∘ indexEquiv) ω ≫ t)
            (Category.assoc
              (Sigma.reindex indexEquiv (fun i ↦ (Z i).left)).hom e.hom X.hom)
        _ = _ := by
          simpa only [componentSchemeIsoComp, Category.assoc,
            Function.comp_apply] using
              congrArg (fun h ↦ (componentSchemeIsoComp ω).hom ≫ h)
                (Sigma.ι_reindex_hom_assoc indexEquiv
                  (fun i ↦ (Z i).left) ω (e.hom ≫ X.hom))
    have hlast :
        (componentSchemeIso ω).hom ≫
            Sigma.ι (fun i ↦ (Z i).left) (indexEquiv ω) ≫
              e.hom ≫ X.hom = Sigma.ι YS ω ≫ Sigma.desc hS := by
      have h1 :
          (componentSchemeIso ω).hom ≫
              (Sigma.ι (fun i ↦ (Z i).left) (indexEquiv ω) ≫
                (e.hom ≫ X.hom)) =
            (componentSchemeIso ω).hom ≫
              (Sigma.ι (fun i ↦ (Z i).left) (indexEquiv ω) ≫
                Sigma.desc (fun i ↦ (Z i).hom)) :=
        congrArg
          (fun t ↦ (componentSchemeIso ω).hom ≫
            (Sigma.ι (fun i ↦ (Z i).left) (indexEquiv ω) ≫ t)) heZ
      have h2 :
          (componentSchemeIso ω).hom ≫
              (Sigma.ι (fun i ↦ (Z i).left) (indexEquiv ω) ≫
                Sigma.desc (fun i ↦ (Z i).hom)) =
            (componentSchemeIso ω).hom ≫ (Z (indexEquiv ω)).hom :=
        congrArg (fun t ↦ (componentSchemeIso ω).hom ≫ t)
          (Sigma.ι_comp_desc (fun i ↦ (Z i).hom) (indexEquiv ω))
      have h3 :
          (componentSchemeIso ω).hom ≫ (Z (indexEquiv ω)).hom =
            Sigma.ι YS ω ≫ Sigma.desc hS := by
        change (componentIso ω).hom.left ≫
          (Z (indexEquiv ω)).hom =
            Sigma.ι YS ω ≫ Sigma.desc hS
        exact (MorphismProperty.Over.w (componentIso ω).hom).trans hιS.symm
      exact h1.trans (h2.trans h3)
    exact hmid.trans hlast
  exact MorphismProperty.Over.isoMk totalIso htotal

private lemma geometricFiber_map_injective
    {X Y : (Spec (.of k)).Etale} {f g : X ⟶ Y}
    (h : (geometricFiber k K).map f = (geometricFiber k K).map g) :
    f = g := by
  apply MorphismProperty.Over.Hom.ext
  obtain ⟨L, a, e, hField, hFiniteSep, he⟩ :=
    exists_iso_sigmaSpec k X
  rw [← cancel_epi e.hom]
  apply Sigma.hom_ext
  intro i
  let : Field (L i) := (hField i).toField
  let : Algebra k (L i) := (a i).hom.toAlgebra
  have hfs := hFiniteSep i
  let : Module.Finite k (L i) := hfs.1
  let : Algebra.IsSeparable k (L i) := hfs.2
  let φ : L i →ₐ[k] K := IsSepClosed.lift
  let x₀ : Spec (.of K) ⟶ Spec (L i) :=
    Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hff : φ.toRingHom.FaithfullyFlat := by
    let : Algebra (L i) K := φ.toRingHom.toAlgebra
    let : Module.Free (L i) K := Module.Free.of_divisionRing (L i) K
    let : Module.Flat (L i) K := Module.Flat.of_free
    let : IsLocalHom (algebraMap (L i) K) := by
      change IsLocalHom φ.toRingHom
      infer_instance
    rw [← RingHom.algebraMap_toAlgebra φ.toRingHom,
      RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hflatSurj :
      AlgebraicGeometry.Flat x₀ ∧ AlgebraicGeometry.Surjective x₀ :=
    (AlgebraicGeometry.flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom φ.toRingHom)).mpr hff
  let : AlgebraicGeometry.Flat x₀ := hflatSurj.1
  let : AlgebraicGeometry.Surjective x₀ := hflatSurj.2
  let : Epi x₀ := AlgebraicGeometry.Flat.epi_of_flat_of_surjective x₀
  let x : Over.mk (ξ k K) ⟶ X.toComma :=
    Over.homMk
      (x₀ ≫ Sigma.ι (fun j ↦ Spec (L j)) i ≫ e.hom) (by
        change (x₀ ≫ Sigma.ι (fun j ↦ Spec (L j)) i ≫ e.hom) ≫
          X.hom = ξ k K
        calc
          (x₀ ≫ Sigma.ι (fun j ↦ Spec (L j)) i ≫ e.hom) ≫ X.hom =
              x₀ ≫ (Sigma.ι (fun j ↦ Spec (L j)) i ≫
                (e.hom ≫ X.hom)) := by
            simp only [Category.assoc]
          _ = x₀ ≫ (Sigma.ι (fun j ↦ Spec (L j)) i ≫
                Sigma.desc (fun j ↦ Spec.map (a j))) :=
            congrArg
              (fun m ↦ x₀ ≫ (Sigma.ι (fun j ↦ Spec (L j)) i ≫ m)) he
          _ = x₀ ≫ Spec.map (a i) :=
            congrArg (fun m ↦ x₀ ≫ m)
              (Sigma.ι_comp_desc (fun j ↦ Spec.map (a j)) i)
          _ = ξ k K := by
            dsimp only [x₀]
            have hring :
                a i ≫ CommRingCat.ofHom φ.toRingHom =
                  CommRingCat.ofHom (algebraMap k K) := by
              ext z
              exact φ.commutes z
            exact (Spec.map_comp (a i)
              (CommRingCat.ofHom φ.toRingHom)).symm.trans
                (congrArg Spec.map hring))
  have hx := congrArg (fun q ↦ q.hom.hom.hom x) h
  change x ≫ f.hom = x ≫ g.hom at hx
  have hxLeft := congrArg (fun q ↦ q.left) hx
  change
    (x₀ ≫ Sigma.ι (fun j ↦ Spec (L j)) i ≫ e.hom) ≫ f.left =
      (x₀ ≫ Sigma.ι (fun j ↦ Spec (L j)) i ≫ e.hom) ≫ g.left at hxLeft
  rw [← cancel_epi x₀]
  simpa only [Category.assoc] using hxLeft

private instance geometricFiberFaithful :
    (geometricFiber k K).Faithful where
  map_injective h := geometricFiber_map_injective k K h

private noncomputable def geometricFiberCounitComponent
    (S : DiscreteContAction TopCat (G k K)) :
    (geometricFiber k K).obj ((inverseFunctor k K).obj S) ≅ S :=
  (inverseCounitIso k K).app S

private lemma geometricFiberCounitComponent_naturality
    {S T : DiscreteContAction TopCat (G k K)} (f : S ⟶ T) :
    (geometricFiber k K).map ((inverseFunctor k K).map f) ≫
        (geometricFiberCounitComponent k K T).hom =
      (geometricFiberCounitComponent k K S).hom ≫ f := by
  exact (inverseCounitIso k K).hom.naturality f

private noncomputable def unitDefect
    (X : (Spec (.of k)).Etale) :
    (geometricFiber k K).obj X ≅ (geometricFiber k K).obj X :=
  ((geometricFiber k K).mapIso
    (uncorrectedUnitObjIso k K X)).symm ≪≫
      geometricFiberCounitComponent k K ((geometricFiber k K).obj X)

private noncomputable def unitComponent
    (X : (Spec (.of k)).Etale) :
    X ≅ (inverseFunctor k K).obj ((geometricFiber k K).obj X) :=
  (uncorrectedUnitObjIso k K X).symm ≪≫
    (inverseFunctor k K).mapIso (unitDefect k K X).symm

private lemma unitComponent_triangle
    (X : (Spec (.of k)).Etale) :
    (geometricFiber k K).map (unitComponent k K X).hom ≫
        (geometricFiberCounitComponent k K
          ((geometricFiber k K).obj X)).hom =
      𝟙 ((geometricFiber k K).obj X) := by
  simp only [unitComponent, unitDefect, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [Functor.map_comp, Category.assoc]
  rw [geometricFiberCounitComponent_naturality]
  simp

private noncomputable def unitIso :
    𝟭 ((Spec (.of k)).Etale) ≅
      geometricFiber k K ⋙ inverseFunctor k K :=
  NatIso.ofComponents (fun X ↦ by
    change X ≅
      (inverseFunctor k K).obj ((geometricFiber k K).obj X)
    exact unitComponent k K X) (fun {X Y} f ↦ by
    change f ≫ (unitComponent k K Y).hom =
      (unitComponent k K X).hom ≫
        (inverseFunctor k K).map ((geometricFiber k K).map f)
    apply (geometricFiber k K).map_injective
    apply (cancel_mono (geometricFiberCounitComponent k K
      ((geometricFiber k K).obj Y)).hom).1
    calc
      (geometricFiber k K).map (f ≫ (unitComponent k K Y).hom) ≫
          (geometricFiberCounitComponent k K
            ((geometricFiber k K).obj Y)).hom =
          (geometricFiber k K).map f ≫
            ((geometricFiber k K).map (unitComponent k K Y).hom ≫
              (geometricFiberCounitComponent k K
                ((geometricFiber k K).obj Y)).hom) := by
              rw [Functor.map_comp, Category.assoc]
      _ = (geometricFiber k K).map f := by
        rw [unitComponent_triangle k K Y, Category.comp_id]
      _ = ((geometricFiber k K).map (unitComponent k K X).hom ≫
            (geometricFiberCounitComponent k K
              ((geometricFiber k K).obj X)).hom) ≫
              (geometricFiber k K).map f := by
        rw [unitComponent_triangle k K X, Category.id_comp]
      _ = (geometricFiber k K).map (unitComponent k K X).hom ≫
            ((geometricFiberCounitComponent k K
              ((geometricFiber k K).obj X)).hom ≫
                (geometricFiber k K).map f) :=
        Category.assoc _ _ _
      _ = (geometricFiber k K).map (unitComponent k K X).hom ≫
            ((geometricFiber k K).map
              ((inverseFunctor k K).map ((geometricFiber k K).map f)) ≫
                (geometricFiberCounitComponent k K
                  ((geometricFiber k K).obj Y)).hom) := by
        rw [geometricFiberCounitComponent_naturality]
      _ = (geometricFiber k K).map
            ((unitComponent k K X).hom ≫
              (inverseFunctor k K).map ((geometricFiber k K).map f)) ≫
                (geometricFiberCounitComponent k K
                  ((geometricFiber k K).obj Y)).hom := by
        rw [Functor.map_comp, Category.assoc])

/-
The assembled equivalence remains private so the implementation-only inverse,
unit, counit, and triangle declarations do not become public API.
-/
private noncomputable def assembledEquivalence :
    (Spec (.of k)).Etale ≌
      DiscreteContAction TopCat (K ≃ₐ[k] K) where
  functor := geometricFiber k K
  inverse := inverseFunctor k K
  unitIso := unitIso k K
  counitIso := inverseCounitIso k K
  functor_unitIso_comp X := unitComponent_triangle k K X

/-- **Stacks Project, Tag 03QR.**  Étale schemes over a field are
equivalent to discrete continuous sets with an action of its absolute Galois
group.  The forward functor is the geometric fiber at `Spec K`. -/
@[stacks 03QR "The category of schemes étale over a field is equivalent to \
the category of discrete sets with continuous action by its absolute Galois group."]
noncomputable opaque equivDiscreteContAction :
    (Spec (.of k)).Etale ≌
      DiscreteContAction TopCat (K ≃ₐ[k] K) :=
  assembledEquivalence k K

instance geometricFiberIsEquivalence :
    (geometricFiber k K).IsEquivalence :=
  (assembledEquivalence k K).isEquivalence_functor

end AlgebraicGeometry.Scheme.Etale
