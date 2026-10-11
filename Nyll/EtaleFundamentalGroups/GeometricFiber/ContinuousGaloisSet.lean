/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.SchemeTheory.Etale.OverField.Decomposition
public import Nyll.EtaleFundamentalGroups.ContinuousActions.TopCatCompat

/-!
# The geometric fiber as a continuous Galois set

This file constructs the forward functor in Stacks Project, Tag `03QR`.
For a separable closure `K/k`, an étale `k`-scheme is sent to its set of
geometric points, with the discrete topology and the natural continuous
action of `K ≃ₐ[k] K` by precomposition.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits MorphismProperty
open scoped AlgebraicGeometry.FiniteEtale

namespace AlgebraicGeometry.Scheme.Etale

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]

/-- The Galois action on geometric points is precomposition by the
corresponding automorphism of `Spec K`. -/
local instance geometricFiberMulAction
    (X : (Spec (.of k)).Etale) :
    MulAction (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) where
  smul g x := by
    let σ : (Over.mk (ξ k K)).left ⟶ (Over.mk (ξ k K)).left := by
      change Spec (.of K) ⟶ Spec (.of K)
      exact Spec.map (CommRingCat.ofHom (g : K →+* K))
    let σOver : Over.mk (ξ k K) ⟶ Over.mk (ξ k K) :=
      Over.homMk σ (by
        change Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ ξ k K = ξ k K
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgEquiv.toAlgHom_toRingHom,
          AlgHom.comp_algebraMap])
    exact σOver ≫ x
  one_smul x := by
    ext1
    change Spec.map (CommRingCat.ofHom ((1 : K ≃ₐ[k] K) : K →+* K)) ≫ x.left = x.left
    simp [AlgEquiv.aut_one]
  mul_smul g h x := by
    ext1
    change Spec.map (CommRingCat.ofHom ((g * h : K ≃ₐ[k] K) : K →+* K)) ≫ x.left =
      Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫
        Spec.map (CommRingCat.ofHom (h : K →+* K)) ≫ x.left
    simp [AlgEquiv.aut_mul, Category.assoc]

omit [IsSepClosure k K] in
@[simp]
private lemma geometricFiber_smul_left (X : (Spec (.of k)).Etale)
    (g : K ≃ₐ[k] K) (x : Over.mk (ξ k K) ⟶ X.toComma) :
    (g • x).left = Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ x.left :=
  rfl

/-- Geometric fibers are given the discrete topology. -/
local instance geometricFiberTopologicalSpace (X : (Spec (.of k)).Etale) :
    TopologicalSpace (Over.mk (ξ k K) ⟶ X.toComma) :=
  ⊥

local instance geometricFiberDiscreteTopology (X : (Spec (.of k)).Etale) :
    DiscreteTopology (Over.mk (ξ k K) ⟶ X.toComma) :=
  discreteTopology_bot _

omit [IsSepClosure k K] in
/-- A geometric point of an étale scheme over a field factors through one
finite étale component of the decomposition in Tag `02GL`. -/
private lemma exists_finiteEtale_factorization
    (X : (Spec (.of k)).Etale)
    (x : Over.mk (ξ k K) ⟶ X.toComma) :
    ∃ (Y : AlgebraicGeometry.FiniteEtale (Spec (.of k)))
      (f : Y.toComma ⟶ X.toComma)
      (y : Over.mk (ξ k K) ⟶ Y.toComma),
      y ≫ f = x := by
  obtain ⟨L, a, e, hField, hFiniteSep, he⟩ := exists_iso_sigmaSpec k X
  let z : Spec (.of K) ⟶ (∐ fun i ↦ Spec (L i)) := x.left ≫ e.inv
  let c : Spec (.of K) := IsLocalRing.closedPoint K
  let q : Σ i, Spec (L i) :=
    (sigmaMk (fun i ↦ Spec (L i))).symm (z c)
  let i : X.left := q.1
  let p : Spec (L i) := q.2
  have hq :
      Sigma.ι (fun i ↦ Spec (L i)) i p = z c := by
    rw [← sigmaMk_mk]
    simp [i, p, q]
  let inclusion : Spec (L i) ⟶ (∐ fun i ↦ Spec (L i)) :=
    Sigma.ι (fun i ↦ Spec (L i)) i
  have : IsOpenImmersion (inclusion ≫ sigmaSpec L) := by
    dsimp only [inclusion]
    rw [ι_sigmaSpec]
    infer_instance
  let : IsOpenImmersion inclusion :=
    IsOpenImmersion.of_comp inclusion (sigmaSpec L)
  have hz : Set.range z ⊆ Set.range inclusion := by
    rintro _ ⟨t, rfl⟩
    have hc : z c ∈ inclusion.opensRange := ⟨p, hq⟩
    have ht : z t ∈ inclusion.opensRange :=
      ((IsLocalRing.specializes_closedPoint t).map z.continuous).mem_open
        inclusion.opensRange.2 hc
    rw [← Scheme.Hom.coe_opensRange]
    exact ht
  let l : Spec (.of K) ⟶ Spec (L i) :=
    IsOpenImmersion.lift inclusion z hz
  have hlift : l ≫ inclusion = z :=
    IsOpenImmersion.lift_fac inclusion z hz
  let : Field (L i) := (hField i).toField
  let : Algebra k (L i) := (a i).hom.toAlgebra
  have hfs : Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i) :=
    hFiniteSep i
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
  let b : Spec (L i) ⟶ Spec (.of k) := Spec.map (a i)
  let : IsFiniteEtale b := by
    rw [IsFiniteEtale.SpecMap_iff]
    change Algebra.FiniteEtale k (L i)
    infer_instance
  let Y : AlgebraicGeometry.FiniteEtale (Spec (.of k)) :=
    AlgebraicGeometry.FiniteEtale.mk b
  let j : Spec (L i) ⟶ X.left := inclusion ≫ e.hom
  have hj : j ≫ X.hom = b := by
    calc
      j ≫ X.hom = inclusion ≫ (e.hom ≫ X.hom) := by
        dsimp only [j]
        rw [Category.assoc]
      _ = inclusion ≫ Sigma.desc (fun i ↦ Spec.map (a i)) :=
        congrArg (fun q ↦ inclusion ≫ q) he
      _ = Spec.map (a i) := Sigma.ι_comp_desc _ _
      _ = b := rfl
  let f : Y.toComma ⟶ X.toComma := Over.homMk j hj
  have hlj : l ≫ j = x.left := by
    dsimp [j]
    rw [← Category.assoc, hlift]
    simp [z]
  let y : Over.mk (ξ k K) ⟶ Y.toComma :=
    Over.homMk l (by
      change l ≫ b = ξ k K
      exact
        (congrArg (fun q ↦ l ≫ q) hj.symm).trans <|
          (Category.assoc l j X.hom).symm.trans <|
            (congrArg (fun q ↦ q ≫ X.hom) hlj).trans x.w)
  refine ⟨Y, f, y, ?_⟩
  ext1
  exact hlj

/-- The action on the geometric fiber of an arbitrary étale scheme is
continuous.  Openness is reduced to the finite component through which the
chosen geometric point factors. -/
local instance geometricFiberContinuousSMul (X : (Spec (.of k)).Etale) :
    ContinuousSMul (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  obtain ⟨Y, f, y, hy⟩ := exists_finiteEtale_factorization k K X x
  rw [← hy]
  let : TopologicalSpace (Over.mk (ξ k K) ⟶ Y.toComma) := ⊥
  let : DiscreteTopology (Over.mk (ξ k K) ⟶ Y.toComma) :=
    discreteTopology_bot _
  have hyContinuous :
      ContinuousSMul (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ Y.toComma) :=
    inferInstance
  have hyOpen :
      IsOpen (MulAction.stabilizer (K ≃ₐ[k] K) y : Set (K ≃ₐ[k] K)) :=
    (continuousSMul_iff_stabilizer_isOpen.mp hyContinuous) y
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer (K ≃ₐ[k] K) y) ?_ hyOpen
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  have hgLeft := congrArg (fun z ↦ z.left) hg
  change Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ y.left = y.left at hgLeft
  ext1
  change Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫
      (y.left ≫ f.left) = y.left ≫ f.left
  rw [← Category.assoc, hgLeft]

/-- The forward functor in Tag `03QR`: an étale `k`-scheme is sent to its
discrete continuous set of `K`-valued geometric points. -/
@[stacks 03QR "the geometric-fiber functor from étale schemes to discrete continuous Galois sets"]
noncomputable def geometricFiber :
    (Spec (.of k)).Etale ⥤ DiscreteContAction TopCat (K ≃ₐ[k] K) := by
  let actionFunctor :
      (Spec (.of k)).Etale ⥤ Action TopCat (K ≃ₐ[k] K) :=
    { obj := fun X ↦
        { V := TopCat.of (Over.mk (ξ k K) ⟶ X.toComma)
          ρ :=
            { toFun := fun g ↦ TopCat.ofHom
                ⟨fun x ↦ g • x, continuous_of_discreteTopology⟩
              map_one' := by
                apply TopCat.ext
                intro x
                exact one_smul _ x
              map_mul' := by
                intro g h
                apply TopCat.ext
                intro x
                exact mul_smul g h x } }
      map := fun {X Y} f ↦
        { hom := TopCat.ofHom
            ⟨fun x ↦ x ≫ f.hom, continuous_of_discreteTopology⟩
          comm := fun g ↦ by
            apply TopCat.ext
            intro x
            apply Over.OverMorphism.ext
            change
              (Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ x.left) ≫ f.hom.left =
                Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫
                  (x.left ≫ f.hom.left)
            exact Category.assoc _ _ _ }
      map_id := fun X ↦ by
        apply Action.hom_ext
        apply TopCat.ext
        intro x
        exact Category.comp_id x
      map_comp := fun f g ↦ by
        apply Action.hom_ext
        apply TopCat.ext
        intro x
        exact (Category.assoc x f.hom g.hom).symm }
  let continuousFunctor :
      (Spec (.of k)).Etale ⥤ ContAction TopCat (K ≃ₐ[k] K) :=
    ObjectProperty.lift _ actionFunctor (fun X ↦ by
      apply (Action.isContinuous_def (actionFunctor.obj X)).2
      change Continuous (fun p :
        (K ≃ₐ[k] K) × (Over.mk (ξ k K) ⟶ X.toComma) ↦ p.1 • p.2)
      exact continuous_smul)
  exact ObjectProperty.lift _ continuousFunctor (fun X ↦ by
    change DiscreteTopology (Over.mk (ξ k K) ⟶ X.toComma)
    infer_instance)

end AlgebraicGeometry.Scheme.Etale
