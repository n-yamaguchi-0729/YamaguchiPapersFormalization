/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.IntegralClosure.FiniteProduct
import EtaleFundamentalGroups.Purity.PuncturedSpectrumNormalizationExtension
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.HeightTwo
import SchemeTheory.Etale.OverField.Decomposition
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Finiteness of the normalization across a punctured regular local spectrum

This file studies the generic fibre of a finite-etale cover of a punctured
two-dimensional regular local spectrum.  The generic fibre is a finite
etale algebra over the function field and hence a finite product of finite
separable field extensions.  This decomposition supplies the finite algebra
needed to prove that the relative normalization over the full local spectrum
is finite.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]

private theorem puncturedSpectrum_nonempty_dimension_two
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    Nonempty (Scheme.puncturedSpectrum R) := by
  apply Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R
  rw [hdim]
  norm_num

omit [IsDomain R] in
private theorem puncturedSpectrumInclusion_isOpenImmersion :
    IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
  dsimp only [Scheme.puncturedSpectrumInclusion]
  infer_instance

/-- The generic point of the full spectrum, lifted canonically through the
punctured open subscheme. -/
noncomputable def puncturedSpectrumGenericMorphism
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    Spec (.of (Spec (.of R)).functionField) ⟶ Scheme.puncturedSpectrum R := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  letI : Nonempty U := puncturedSpectrum_nonempty_dimension_two R hdim
  letI : IsOpenImmersion j := puncturedSpectrumInclusion_isOpenImmersion R
  letI : IsIntegral X := inferInstance
  letI : IsIntegral U := isIntegral_of_isOpenImmersion j
  let ηX : Spec (.of X.functionField) ⟶ X :=
    X.genericExtensionMorphism X.functionField
  apply IsOpenImmersion.lift j ηX
  rintro _ ⟨x, rfl⟩
  refine ⟨genericPoint U, ?_⟩
  rw [genericPoint_eq_of_isOpenImmersion j]
  rw [Subsingleton.elim x (IsLocalRing.closedPoint (CommRingCat.of X.functionField))]
  exact (X.genericExtensionMorphism_apply_closedPoint X.functionField).symm

@[reassoc (attr := simp)]
theorem puncturedSpectrumGenericMorphism_comp_inclusion
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    puncturedSpectrumGenericMorphism R hdim ≫
        Scheme.puncturedSpectrumInclusion R =
      (Spec (.of R)).genericExtensionMorphism
        (Spec (.of R)).functionField := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let : Nonempty U := puncturedSpectrum_nonempty_dimension_two R hdim
  let : IsOpenImmersion j := puncturedSpectrumInclusion_isOpenImmersion R
  let : IsIntegral X := inferInstance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  change IsOpenImmersion.lift j
      (X.genericExtensionMorphism X.functionField) _ ≫ j = _
  exact IsOpenImmersion.lift_fac _ _ _

/-- The generic fibre of a finite-etale cover of the punctured spectrum. -/
noncomputable def puncturedSpectrumGenericFiber
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    FiniteEtale (Spec (.of (Spec (.of R)).functionField)) :=
  (FiniteEtale.pullback (puncturedSpectrumGenericMorphism R hdim)).obj W

/-- The projection from the generic fibre back to the punctured cover. -/
noncomputable def puncturedSpectrumGenericFiberToCover
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    (puncturedSpectrumGenericFiber R hdim W).left ⟶ W.left :=
  pullback.fst W.hom (puncturedSpectrumGenericMorphism R hdim)

@[reassoc (attr := simp)]
theorem puncturedSpectrumGenericFiberToCover_comp
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    puncturedSpectrumGenericFiberToCover R hdim W ≫ W.hom =
      (puncturedSpectrumGenericFiber R hdim W).hom ≫
        puncturedSpectrumGenericMorphism R hdim := by
  exact pullback.condition

private theorem puncturedSpectrumGenericMorphism_denseRange
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞)) :
    DenseRange (puncturedSpectrumGenericMorphism R hdim) := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let j : U ⟶ X := Scheme.puncturedSpectrumInclusion R
  let η := puncturedSpectrumGenericMorphism R hdim
  let : Nonempty U := puncturedSpectrum_nonempty_dimension_two R hdim
  let : IsOpenImmersion j := puncturedSpectrumInclusion_isOpenImmersion R
  let : IsIntegral X := inferInstance
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  have hη (x : Spec (.of X.functionField)) : η x = genericPoint U := by
    apply j.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply,
      puncturedSpectrumGenericMorphism_comp_inclusion R hdim,
      Subsingleton.elim x
        (IsLocalRing.closedPoint (CommRingCat.of X.functionField)),
      X.genericExtensionMorphism_apply_closedPoint,
      genericPoint_eq_of_isOpenImmersion j]
  have hrange : Set.range η = {genericPoint U} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_singleton_iff.mpr (hη x)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨IsLocalRing.closedPoint (CommRingCat.of X.functionField), hη _⟩
  rw [denseRange_iff_closure_range, hrange, genericPoint_closure]

/-- The generic-fibre projection is schematically dominant; in particular,
it injects the global sections of the punctured cover into those of its
generic fibre. -/
theorem puncturedSpectrumGenericFiberToCover_appTop_injective
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    Function.Injective
      (puncturedSpectrumGenericFiberToCover R hdim W).appTop.hom := by
  let X := Spec (.of R)
  let U := Scheme.puncturedSpectrum R
  let η := puncturedSpectrumGenericMorphism R hdim
  let G := puncturedSpectrumGenericFiber R hdim W
  let q : G.left ⟶ W.left := puncturedSpectrumGenericFiberToCover R hdim W
  let : Nonempty U := puncturedSpectrum_nonempty_dimension_two R hdim
  let : IsIntegral X := inferInstance
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) :=
    puncturedSpectrumInclusion_isOpenImmersion R
  let : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let : IsDominant η :=
    ⟨puncturedSpectrumGenericMorphism_denseRange R hdim⟩
  let hstd : IsSchemeTheoreticallyDominant η :=
    IsSchemeTheoreticallyDominant.of_isDominant η
  let : QuasiSeparatedSpace U := inferInstance
  let : QuasiCompact η := inferInstance
  let hflat : Flat W.hom :=
    Etale.iff_flat_and_formallyUnramified.mp W.prop.toEtale |>.1
  let : IsSchemeTheoreticallyDominant q := by
    dsimp only [q, puncturedSpectrumGenericFiberToCover]
    exact @IsSchemeTheoreticallyDominant.pullbackFst _ _ _
      W.hom η hstd (inferInstance : QuasiCompact η) hflat
  let : QuasiCompact q := by
    dsimp only [q, puncturedSpectrumGenericFiberToCover]
    have hbase : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u})
        (fun {_ _} f => QuasiCompact f) := quasiCompact_isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} f => QuasiCompact f)
      (IsPullback.of_hasPullback W.hom η).flip (inferInstance : QuasiCompact η)
  exact q.app_injective ⊤

/-- The canonical function-field algebra structure on the global sections
of the generic fibre. -/
@[reducible] noncomputable def puncturedSpectrumGenericFiberAlgebra
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    Algebra (Spec (.of R)).functionField
      Γ((puncturedSpectrumGenericFiber R hdim W).left, ⊤) :=
  let K : Type u := (Spec (.of R)).functionField
  let G := puncturedSpectrumGenericFiber R hdim W
  (G.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra

/-- The section algebra of the generic fibre is finite etale over the
function field. -/
theorem puncturedSpectrumGenericFiber_sections_etale
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    letI := puncturedSpectrumGenericFiberAlgebra R hdim W
    Algebra.Etale (Spec (.of R)).functionField
      Γ((puncturedSpectrumGenericFiber R hdim W).left, ⊤) := by
  let K : Type u := (Spec (.of R)).functionField
  let G := puncturedSpectrumGenericFiber R hdim W
  let f : G.left ⟶ Spec (.of K) := G.hom
  let : Algebra K Γ(G.left, ⊤) :=
    puncturedSpectrumGenericFiberAlgebra R hdim W
  let : IsFiniteEtale f := G.prop
  let : IsFinite f := G.prop.toIsFinite
  let : IsAffineHom f := G.prop.toIsFinite.toIsAffineHom
  let : IsAffine G.left := isAffine_of_isAffineHom f
  have hf : f.appTop.hom.Etale := by
    rw [← HasRingHomProperty.iff_of_isAffine
      (P := @AlgebraicGeometry.Etale)]
    exact G.prop.toEtale
  change (f.appTop.hom.comp
    (Scheme.ΓSpecIso (.of K)).inv.hom).Etale
  exact RingHom.Etale.respectsIso.right f.appTop.hom
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm hf

/-- Global sections of the generic fibre split as a finite product of
finite separable extensions of the function field. -/
theorem puncturedSpectrumGenericFiber_sections_decomposition
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    let K : Type u := (Spec (.of R)).functionField
    let C := Γ((puncturedSpectrumGenericFiber R hdim W).left, ⊤)
    letI := puncturedSpectrumGenericFiberAlgebra R hdim W
    ∃ (I : Type u) (_ : Finite I) (L : I → Type u)
      (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i))
      (_ : C ≃ₐ[K] ∀ i, L i),
      ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) := by
  let K : Type u := (Spec (.of R)).functionField
  let G := puncturedSpectrumGenericFiber R hdim W
  let C := Γ(G.left, ⊤)
  let : Algebra K C := puncturedSpectrumGenericFiberAlgebra R hdim W
  let : Algebra.Etale K C :=
    puncturedSpectrumGenericFiber_sections_etale R hdim W
  exact (Algebra.Etale.iff_exists_algEquiv_prod K C).mp inferInstance

omit [IsRegularLocalRing R] in
private theorem genericExtensionMorphism_appTop_eq_germ :
    let X := Spec (.of R)
    let K : Type u := X.functionField
    letI : IsIntegral X := inferInstance
    letI : Nonempty (⊤ : X.Opens) :=
      ⟨⟨genericPoint X, by simp⟩⟩
    (X.genericExtensionMorphism K).appTop.hom =
      (Scheme.ΓSpecIso (.of K)).inv.hom.comp
        (X.germToFunctionField ⊤).hom := by
  let X := Spec (.of R)
  let K : Type u := X.functionField
  let : IsIntegral X := inferInstance
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by simp⟩⟩
  ext r
  let e : Γ(Spec (.of K), ⊤) ≃+* K :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  change (X.genericExtensionMorphism K).appTop.hom r =
    e.symm (X.germToFunctionField ⊤ r)
  apply e.injective
  rw [e.apply_symm_apply]
  change e ((X.genericExtensionMorphism K).app ⊤ r) =
    X.germToFunctionField ⊤ r
  have h := X.genericExtensionSectionsIso_hom_app K ⊤ r
  change e ((X.genericExtensionMorphism K).app ⊤ r) =
    algebraMap K K (X.germToFunctionField ⊤ r) at h
  simpa using h

/-- The injection from the punctured cover to its generic fibre respects
the base section ring, where the latter acts through the function field. -/
theorem puncturedSpectrumGenericFiberToCover_appTop_comp
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    let X := Spec (.of R)
    let K : Type u := X.functionField
    let G := puncturedSpectrumGenericFiber R hdim W
    let q := puncturedSpectrumGenericFiberToCover R hdim W
    let f := puncturedSpectrumCoverToSpec R W
    letI : IsIntegral X := inferInstance
    letI : Nonempty (⊤ : X.Opens) :=
      ⟨⟨genericPoint X, by simp⟩⟩
    q.appTop.hom.comp f.appTop.hom =
      (G.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).comp
        (X.germToFunctionField ⊤).hom := by
  let X := Spec (.of R)
  let K : Type u := X.functionField
  let G := puncturedSpectrumGenericFiber R hdim W
  let η := puncturedSpectrumGenericMorphism R hdim
  let q := puncturedSpectrumGenericFiberToCover R hdim W
  let f := puncturedSpectrumCoverToSpec R W
  let : IsIntegral X := inferInstance
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by simp⟩⟩
  dsimp only
  have hs : q ≫ f =
      (puncturedSpectrumGenericFiber R hdim W).hom ≫
        X.genericExtensionMorphism K := by
    calc
      q ≫ f = (q ≫ W.hom) ≫ Scheme.puncturedSpectrumInclusion R := by
        simp only [f, puncturedSpectrumCoverToSpec, Category.assoc]
      _ = ((puncturedSpectrumGenericFiber R hdim W).hom ≫
          puncturedSpectrumGenericMorphism R hdim) ≫
          Scheme.puncturedSpectrumInclusion R := by
        exact congrArg
          (fun t ↦ t ≫ Scheme.puncturedSpectrumInclusion R)
          (puncturedSpectrumGenericFiberToCover_comp R hdim W)
      _ = (puncturedSpectrumGenericFiber R hdim W).hom ≫
          X.genericExtensionMorphism K := by
        exact congrArg
          (fun t ↦ (puncturedSpectrumGenericFiber R hdim W).hom ≫ t)
          (puncturedSpectrumGenericMorphism_comp_inclusion R hdim)
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hs]
  change (puncturedSpectrumGenericFiber R hdim W).hom.appTop.hom.comp
      (X.genericExtensionMorphism K).appTop.hom = _
  rw [genericExtensionMorphism_appTop_eq_germ (R := R)]
  rfl

/-- The integral closure defining the normalization extension is a finite
module.  The proof is valid for an arbitrary, possibly disconnected,
finite-etale punctured cover. -/
theorem puncturedSpectrumNormalizationExtension_integralClosure_finite
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    let f := puncturedSpectrumCoverToSpec R W
    letI : Algebra Γ(Spec (.of R), ⊤) Γ(W.left, ⊤) :=
      f.appTop.hom.toAlgebra
    Module.Finite Γ(Spec (.of R), ⊤)
      (integralClosure Γ(Spec (.of R), ⊤) Γ(W.left, ⊤)) := by
  let X := Spec (.of R)
  let K : Type u := X.functionField
  let G := puncturedSpectrumGenericFiber R hdim W
  let q := puncturedSpectrumGenericFiberToCover R hdim W
  let f := puncturedSpectrumCoverToSpec R W
  let A : Type u := Γ(X, ⊤)
  let B : Type u := Γ(W.left, ⊤)
  let C : Type u := Γ(G.left, ⊤)
  let : IsIntegrallyClosed R :=
    EtaleFundamentalGroups.SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdim
  let : IsIntegral X := inferInstance
  let : IsNormalIntegral X := inferInstance
  let : IsLocallyNoetherian X := inferInstance
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨genericPoint X, by simp⟩⟩
  let : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian
      (⟨⊤, isAffineOpen_top X⟩ : X.affineOpens)
  let : IsIntegrallyClosed A :=
    IsNormalIntegral.affine_isIntegrallyClosed ⊤ (isAffineOpen_top X)
  let : Algebra A K := (X.germToFunctionField ⊤).hom.toAlgebra
  let : IsFractionRing A K :=
    functionField_isFractionRing_of_isAffineOpen X ⊤
      (isAffineOpen_top X)
  let : Algebra A B := f.appTop.hom.toAlgebra
  let : Algebra K C := puncturedSpectrumGenericFiberAlgebra R hdim W
  let : Algebra A C :=
    ((algebraMap K C).comp (algebraMap A K)).toAlgebra
  let : Algebra B C := q.appTop.hom.toAlgebra
  let : IsScalarTower A K C := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' (by
    change (G.hom.appTop.hom.comp
        (Scheme.ΓSpecIso (.of K)).inv.hom).comp
          (X.germToFunctionField ⊤).hom =
      q.appTop.hom.comp f.appTop.hom
    exact (puncturedSpectrumGenericFiberToCover_appTop_comp R hdim W).symm)
  obtain ⟨I, hI, L, hLField, hLAlgebra, e, hL⟩ :=
    puncturedSpectrumGenericFiber_sections_decomposition R hdim W
  let : Finite I := hI
  let (i : I) : Field (L i) := hLField i
  let (i : I) : Algebra K (L i) := hLAlgebra i
  let (i : I) : Module.Finite K (L i) := (hL i).1
  let (i : I) : Algebra.IsSeparable K (L i) := (hL i).2
  let (i : I) : Algebra A (L i) :=
    ((algebraMap K (L i)).comp (algebraMap A K)).toAlgebra
  let (i : I) : IsScalarTower A K (L i) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A (∀ i, L i) := Pi.algebra (R := A) I L
  let : Algebra K (∀ i, L i) := Pi.algebra (R := K) I L
  let : IsScalarTower A K (∀ i, L i) := inferInstance
  let eA : C ≃ₐ[A] (∀ i, L i) := e.restrictScalars A
  let qA : B →ₐ[A] C := IsScalarTower.toAlgHom A B C
  let φ : B →ₐ[A] (∀ i, L i) := eA.toAlgHom.comp qA
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply puncturedSpectrumGenericFiberToCover_appTop_injective R hdim W
    have hq : algebraMap B C x = algebraMap B C y := eA.injective hxy
    change q.appTop.hom x = q.appTop.hom y at hq
    exact hq
  let φInt := φ.mapIntegralClosure
  have hφInt : Function.Injective φInt := by
    intro x y hxy
    apply Subtype.ext
    apply hφ
    exact congrArg Subtype.val hxy
  let (i : I) : Module.Finite A (integralClosure A (L i)) :=
    IsIntegralClosure.finite A K (L i) (integralClosure A (L i))
  let : Module.Finite A (∀ i, integralClosure A (L i)) := inferInstance
  let : Module.Finite A (integralClosure A (∀ i, L i)) :=
    Module.Finite.equiv
      (EtaleFundamentalGroups.integralClosurePiAlgEquiv L).symm.toLinearEquiv
  exact Module.Finite.of_injective φInt.toLinearMap hφInt

/-- The relative normalization of a two-dimensional regular local spectrum
in any finite-etale cover of its puncture is finite. -/
theorem puncturedSpectrumNormalizationExtensionHom_isFinite
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) :
    IsFinite (puncturedSpectrumNormalizationExtensionHom R W) := by
  apply (puncturedSpectrumNormalizationExtensionHom_isFinite_iff_appTop R W).2
  let X := Spec (.of R)
  let f := puncturedSpectrumCoverToSpec R W
  let A : Type u := Γ(X, ⊤)
  let B : Type u := Γ(W.left, ⊤)
  let : IsLocallyNoetherian X := inferInstance
  let : IsFiniteEtale W.hom := W.prop
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) :=
    puncturedSpectrumInclusion_isOpenImmersion R
  let : QuasiCompact f := by
    dsimp only [f, puncturedSpectrumCoverToSpec]
    have hW : QuasiCompact W.hom := inferInstance
    have hj : QuasiCompact (Scheme.puncturedSpectrumInclusion R) :=
      inferInstance
    exact @quasiCompact_comp W.left (Scheme.puncturedSpectrum R) X
      W.hom (Scheme.puncturedSpectrumInclusion R) hW hj
  let : QuasiSeparated f := by
    dsimp only [f, puncturedSpectrumCoverToSpec]
    have hW : QuasiSeparated W.hom := inferInstance
    have hj : QuasiSeparated (Scheme.puncturedSpectrumInclusion R) :=
      inferInstance
    exact @quasiSeparated_comp W.left (Scheme.puncturedSpectrum R) X
      W.hom (Scheme.puncturedSpectrumInclusion R) hW hj
  let : Algebra A B := f.appTop.hom.toAlgebra
  have hfinite : Module.Finite A (integralClosure A B) :=
    puncturedSpectrumNormalizationExtension_integralClosure_finite R hdim W
  change (f.fromNormalization.app (⊤ : X.Opens)).hom.Finite
  rw [f.fromNormalization_app (isAffineOpen_top X)]
  exact RingHom.Finite.comp
    (f.normalizationObjIso (isAffineOpen_top X)).symm.commRingCatIsoToRingEquiv.finite
    (show (algebraMap A (integralClosure A B)).Finite from hfinite)

end AlgebraicGeometry.FiniteEtale
