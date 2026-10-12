/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentEtaleAutomorphisms
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Cyclic automorphisms of connected finite etale covers of the multiplicative line

The original cover is affine. Its actual section algebra is finite etale over the Laurent
polynomial ring and has connected spectrum. Pullback of sections by inverse cover automorphisms
gives an injective group homomorphism into its cyclic algebra automorphism group.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- The categorical automorphism group of an actual connected finite etale cover of the
multiplicative line is cyclic in characteristic zero. -/
theorem isCyclic_aut_of_connected_finite_etale_laurent
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (Y : FiniteEtale (Spec (CommRingCat.of (LaurentPolynomial K))))
    [ConnectedSpace Y.left] : IsCyclic (Aut Y) := by
  let R := CommRingCat.of (LaurentPolynomial K)
  let X := Spec R
  let π : Y.left ⟶ X := Y.hom
  have finiteπ : IsFinite π := Y.prop.toIsFinite
  have etaleπ : Etale π := Y.prop.toEtale
  have affineY : IsAffine Y.left := isAffine_of_isAffineHom π
  have connectedSections : ConnectedSpace (PrimeSpectrum Γ(Y.left, ⊤)) :=
    Y.left.isoSpec.schemeIsoToHomeo.connectedSpace_iff.mp inferInstance
  let sectionAlgebra : Algebra Γ(X, ⊤) Γ(Y.left, ⊤) := Y.hom.appTop.hom.toAlgebra
  have finiteSections : Module.Finite Γ(X, ⊤) Γ(Y.left, ⊤) := π.finite_appTop
  have etaleSections : Algebra.Etale Γ(X, ⊤) Γ(Y.left, ⊤) := by
    have h : π.appTop.hom.Etale :=
      (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)).mp inferInstance
    exact h.toAlgebra
  let baseAlgebra : Algebra (LaurentPolynomial K) Γ(X, ⊤) :=
    (Scheme.ΓSpecIso R).inv.hom.toAlgebra
  let eBase : LaurentPolynomial K ≃ₐ[LaurentPolynomial K] Γ(X, ⊤) :=
    AlgEquiv.ofRingEquiv (f := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv)
      fun _ => rfl
  have finiteBase : Module.Finite (LaurentPolynomial K) Γ(X, ⊤) :=
    Module.Finite.of_surjective eBase.toLinearMap eBase.surjective
  have etaleBase : Algebra.Etale (LaurentPolynomial K) Γ(X, ⊤) := Algebra.Etale.of_equiv eBase
  let laurentAlgebra : Algebra (LaurentPolynomial K) Γ(Y.left, ⊤) :=
    (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom).toAlgebra
  have sectionTower : IsScalarTower (LaurentPolynomial K) Γ(X, ⊤) Γ(Y.left, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have finiteLaurent : Module.Finite (LaurentPolynomial K) Γ(Y.left, ⊤) :=
    Module.Finite.trans Γ(X, ⊤) Γ(Y.left, ⊤)
  have etaleLaurent : Algebra.Etale (LaurentPolynomial K) Γ(Y.left, ⊤) :=
    Algebra.Etale.comp (LaurentPolynomial K) Γ(X, ⊤) Γ(Y.left, ⊤)
  have cyclicSections : IsCyclic (Γ(Y.left, ⊤) ≃ₐ[LaurentPolynomial K] Γ(Y.left, ⊤)) :=
    isCyclic_algEquiv_of_connected_finite_etale_laurent
  let forgetCover : FiniteEtale X ⥤ Scheme := FiniteEtale.forget X ⋙ Over.forget X
  let sectionsAut (σ : Aut Y) : Γ(Y.left, ⊤) ≃ₐ[LaurentPolynomial K] Γ(Y.left, ⊤) :=
    { toRingEquiv :=
        (Scheme.Γ.mapIso ((forgetCover.mapIso σ).symm.op)).commRingCatIsoToRingEquiv
      commutes' := fun r => by
        change σ.inv.hom.left.appTop.hom
          (Y.hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) =
            Y.hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)
        have hw := congrArg Scheme.Hom.appTop (MorphismProperty.Over.w σ.inv)
        exact ConcreteCategory.congr_hom hw ((Scheme.ΓSpecIso R).inv.hom r) }
  let sectionsHom : Aut Y →* (Γ(Y.left, ⊤) ≃ₐ[LaurentPolynomial K] Γ(Y.left, ⊤)) :=
    { toFun := sectionsAut
      map_one' := by
        apply AlgEquiv.ext
        intro r
        rfl
      map_mul' := fun σ τ => by
        apply AlgEquiv.ext
        intro r
        change (σ.inv.hom.left ≫ τ.inv.hom.left).appTop.hom r =
          σ.inv.hom.left.appTop.hom (τ.inv.hom.left.appTop.hom r)
        rw [Scheme.Hom.comp_appTop]
        rfl }
  apply isCyclic_of_injective sectionsHom
  intro σ τ h
  have hinv : σ.inv.hom.left = τ.inv.hom.left := by
    apply ext_of_isAffine
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact congrArg (fun e : Γ(Y.left, ⊤) ≃ₐ[LaurentPolynomial K] Γ(Y.left, ⊤) => e r) h
  apply Iso.symm_bijective.injective
  apply Iso.ext
  apply (forgetCover.map_injective)
  exact hinv

end AnabelianGeometry.GeometricFundamentalGroup
