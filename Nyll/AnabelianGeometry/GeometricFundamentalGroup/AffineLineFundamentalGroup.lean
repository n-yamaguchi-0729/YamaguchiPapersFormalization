/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.AffineLineEtaleAlgebra
import Nyll.SchemeTheory.LocalGeometry.ConnectedDomainStalks
import Nyll.SchemeTheory.LocalGeometry.SmoothStalkNormality
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The etale fundamental group of the affine line in characteristic zero

A connected finite etale cover of `Spec K[T]` is affine and integral. Its actual
section algebra is a finite etale domain over `K[T]`, hence trivial by the normalization
and Riemann--Hurwitz argument. The original scheme morphism is therefore an isomorphism.
The actual geometric fibre functor and Galois reconstruction then give triviality of
the etale fundamental group.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open scoped Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

/-- Every connected finite etale cover of the affine line over an algebraically
closed characteristic-zero field is an isomorphism. -/
theorem isIso_of_connected_finite_etale_affineLine
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {Y : Scheme.{u}} [ConnectedSpace Y]
    (π : Y ⟶ Spec (CommRingCat.of K[X])) [IsFinite π] [Etale π] : IsIso π := by
  let R := CommRingCat.of K[X]
  let X := Spec R
  have affineY : IsAffine Y := isAffine_of_isAffineHom π
  have domainBase : IsDomain Γ(X, ⊤) :=
    Function.Injective.isDomain (Scheme.ΓSpecIso R).hom.hom
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
  have normalBase : IsIntegrallyClosed Γ(X, ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  have noetherian : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π
  have integral : IsIntegral Y := isIntegral_of_connected_of_isDomain_stalk Y
    (fun y => (Smooth.isDomain_and_isIntegrallyClosed_stalk π y).1)
  let sectionAlgebra : Algebra Γ(X, ⊤) Γ(Y, ⊤) := π.appTop.hom.toAlgebra
  have finiteSections : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := π.finite_appTop
  have etaleSections : Algebra.Etale Γ(X, ⊤) Γ(Y, ⊤) := by
    have h : π.appTop.hom.Etale :=
      (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)).mp inferInstance
    exact h.toAlgebra
  let baseAlgebra : Algebra K[X] Γ(X, ⊤) := (Scheme.ΓSpecIso R).inv.hom.toAlgebra
  let eBase : K[X] ≃ₐ[K[X]] Γ(X, ⊤) :=
    AlgEquiv.ofRingEquiv (f := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv)
      fun _ => rfl
  have finiteBase : Module.Finite K[X] Γ(X, ⊤) :=
    Module.Finite.of_surjective eBase.toLinearMap eBase.surjective
  have etaleBase : Algebra.Etale K[X] Γ(X, ⊤) := Algebra.Etale.of_equiv eBase
  let polynomialAlgebra : Algebra K[X] Γ(Y, ⊤) :=
    (π.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom).toAlgebra
  have sectionTower : IsScalarTower K[X] Γ(X, ⊤) Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have finitePolynomial : Module.Finite K[X] Γ(Y, ⊤) :=
    Module.Finite.trans Γ(X, ⊤) Γ(Y, ⊤)
  have etalePolynomial : Algebra.Etale K[X] Γ(Y, ⊤) :=
    Algebra.Etale.comp K[X] Γ(X, ⊤) Γ(Y, ⊤)
  have bijectiveSections := bijective_algebraMap_of_finite_etale_polynomial
    (K := K) (T := Γ(Y, ⊤))
  have compositeIso : IsIso ((Scheme.ΓSpecIso R).inv ≫ π.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr bijectiveSections
  have sectionIso : IsIso π.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso R).inv _
  have affineIso : IsIso (Y.isoSpec.hom ≫ Spec.map π.appTop) := inferInstance
  rw [Scheme.isoSpec_hom_naturality] at affineIso
  exact IsIso.of_isIso_comp_right π X.isoSpec.hom

/-- The actual geometric fibre of a connected finite etale affine-line cover is
a singleton in characteristic zero. -/
theorem subsingleton_fiber_of_connected_affineLine
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {Ω : Type u} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K[X]))
    (Y : FiniteEtale (Spec (CommRingCat.of K[X]))) [ConnectedSpace Y.left] :
    Subsingleton ((fiber ξ).obj Y) := by
  have finiteEtale : IsFiniteEtale Y.hom := Y.prop
  have finite : IsFinite Y.hom := finiteEtale.toIsFinite
  have etale : Etale Y.hom := finiteEtale.toEtale
  have connectedSource : ConnectedSpace ((𝟭 Scheme).obj Y.left) := by
    change ConnectedSpace Y.left
    infer_instance
  have iso : IsIso Y.hom := isIso_of_connected_finite_etale_affineLine Y.hom
  let e : (Limits.pullback Y.hom ξ : Scheme) ≃ₜ Spec (CommRingCat.of Ω) :=
    (asIso (Limits.pullback.snd Y.hom ξ)).schemeIsoToHomeo
  change Subsingleton (Limits.pullback Y.hom ξ : Scheme)
  exact ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩

/-- The actual etale fundamental group of the affine line over an algebraically
closed characteristic-zero field is trivial at every separably closed geometric point. -/
theorem subsingleton_fundamentalGroup_affineLine
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K[X])) :
    Subsingleton π₁ᵉᵗ(ξ) := by
  constructor
  intro σ τ
  apply Iso.ext
  apply (endEquivAutGalois (fiber ξ)).injective
  apply AutGalois.ext
  intro A
  have connected : ConnectedSpace A.obj.left := connectedSpace_left_of_isConnected A.obj
  have singleton : Subsingleton ((fiber ξ).obj A.obj) :=
    subsingleton_fiber_of_connected_affineLine ξ A.obj
  apply evaluation_aut_injective_of_isConnected (fiber ξ) A.obj A.pt
  exact Subsingleton.elim _ _

end AnabelianGeometry.GeometricFundamentalGroup
