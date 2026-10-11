/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
/-
Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Galois.lean
-/

module

public import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
public import SchemeTheory.FiniteEtale.Geometry

/-!
# The category of finite étale morphisms over a connected base is a Galois category

Let `S` be a scheme and denote by `FEt S` the category of finite étale schemes over `S`. Then
`FEt S` is a `PreGaloisCategory`.
-/


@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits


instance {C : Type*} [Category C] {G : Type*} [Group G] [Finite G] [HasFiniteColimits C] :
    HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

instance {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {G : Type*} [Group G] [Finite G]
    [PreservesFiniteColimits F] :
    PreservesColimitsOfShape (SingleObj G) F := by
  obtain ⟨(G' : Type), hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F

namespace AlgebraicGeometry

namespace FiniteEtale

variable (X : Scheme.{u})

/-- The category of finite étale morphisms is a pre-galois category. -/
instance (X : Scheme.{u}) : PreGaloisCategory (FiniteEtale X) where
  hasQuotientsByFiniteGroups G := inferInstance
  monoInducesIsoOnDirectSummand {f g} i hi := by
    let hfg : IsFiniteEtale g.hom := g.2
    let : IsFinite g.hom := hfg.toIsFinite
    let : Etale g.hom := hfg.toEtale
    rw [FiniteEtale.mono_iff] at hi
    obtain ⟨ho, hc⟩ := hi
    let : IsOpenImmersion i.hom.left := ho
    let : IsClosedImmersion i.hom.left := hc
    let A : Set g.left := Set.range i.hom.left.base
    have hA : IsClosed A := i.hom.left.isClosedEmbedding.isClosed_range
    let U : g.left.Opens := ⟨Aᶜ, hA.isOpen_compl⟩
    let hUo : IsOpenImmersion U.ι := by
      dsimp only [U]
      infer_instance
    let hUc : IsClosedImmersion U.ι := by
      apply isClosedImmersion_of_isPreimmersion_of_isClosed
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_mk, isClosed_compl_iff, U, A]
      apply IsOpenImmersion.isOpen_range
    let hUf : IsFinite U.ι := inferInstance
    let hUe : Etale U.ι := inferInstance
    let : IsFinite (U.ι ≫ g.hom) :=
      MorphismProperty.comp_mem
        (W := (@IsFinite : MorphismProperty Scheme.{u})) U.ι g.hom hUf hfg.toIsFinite
    let _ : Etale U.ι := hUe
    let _ : Etale g.hom := hfg.toEtale
    let : Etale (U.ι ≫ g.hom) := inferInstance
    let hU : IsFiniteEtale (U.ι ≫ g.hom) := ⟨⟩
    let u : FiniteEtale X := ⟨Over.mk (U.ι ≫ g.hom), hU⟩
    refine ⟨u, MorphismProperty.Over.homMk U.ι, ⟨?_⟩⟩
    apply isColimitOfReflectsOfMapIsColimit (FiniteEtale.forget X)
    apply isColimitOfReflectsOfMapIsColimit (Over.forget X)
    simp only [Over.forget_map]
    apply Nonempty.some
    refine nonempty_isColimit_binaryCofanMk_of_isCompl
      i.hom.left U.ι ?_
    constructor
    · rw [disjoint_iff]
      ext x
      simp only [Scheme.Hom.coe_opensRange, U, A,
        TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot, Set.mem_inter_iff,
        Set.mem_range]
      constructor
      · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
        exact (z.property ⟨y, hy.trans hz.symm⟩).elim
      · intro hx
        exact hx.elim
    · rw [codisjoint_iff]
      ext x
      simp only [Scheme.Hom.coe_opensRange, U, A,
        TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union,
        Set.mem_range, Set.mem_univ, iff_true]
      by_cases h : ∃ y, (MorphismProperty.Comma.Hom.hom i).left y = x
      · exact Or.inl h
      · exact Or.inr ⟨⟨x, h⟩, rfl⟩


variable {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)
variable {X}

/-- Pull back finite etale schemes along the field point and take their finite sets of points. -/
def fiber : FiniteEtale X ⥤ FintypeCat :=
  pullback ξ ⋙ forgetScheme Ω

variable {ξ} in
/-- Project a point of a finite etale fiber to the underlying point of its source scheme. -/
def fiberPt {A : FiniteEtale X} (x : (fiber ξ).obj A) : A.left :=
  (pullback.fst A.hom ξ).base x

instance : PreservesFiniteLimits (pullback ξ) := by
  dsimp [pullback]
  apply AffineAnd.preservesFiniteLimits_pullback


instance [ConnectedSpace X] [IsSepClosed Ω] : (fiber ξ).ReflectsIsomorphisms := by
  dsimp [fiber]
  infer_instance

instance [IsSepClosed Ω] : PreservesFiniteColimits (fiber ξ) := by
  dsimp [fiber]
  apply Limits.comp_preservesFiniteColimits

open PreGaloisCategory

/-- If `X` is a connected scheme and `ξ : Spec Ω ⟶ X` is a geometric point,
taking fibers over `ξ` is a fiber functor. -/
instance fiberFunctor [ConnectedSpace X] [IsSepClosed Ω] : FiberFunctor (fiber ξ) where
  preservesTerminalObjects := by dsimp [fiber]; infer_instance
  preservesPullbacks := by dsimp [fiber]; infer_instance
  preservesQuotientsByFiniteGroups _ _ := inferInstance

/-- If `X` is a connected scheme, the category of finite étale schemes over `X`
is a Galois category. -/
instance galoisCategory [ConnectedSpace X] : GaloisCategory (FiniteEtale X) where
  hasFiberFunctor := by
    have : Nonempty X := inferInstance
    let x : X := ‹Nonempty X›.some
    let k : Type u := X.residueField x
    let Ω : Type u := AlgebraicClosure k
    let ξ : Spec (.of Ω) ⟶ X :=
      Spec.map (CommRingCat.ofHom <| algebraMap k Ω) ≫ X.fromSpecResidueField x
    exact ⟨fiber ξ, inferInstance⟩

/-- The étale fundamental group of a connected scheme `X` at the geometric point `ξ` is
the automorphism group of the fiber functor at `ξ`. -/
notation:arg "π₁ᵉᵗ" "(" x ")" => Aut (fiber x)


end AlgebraicGeometry.FiniteEtale
