/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Nyll.SchemeTheory.Normalization.IntegralClosure.FiniteProduct
import Mathlib.RingTheory.Etale.Field

/-!
# Normalization of all generic tensor components

If `L / K` is finite separable, then `F ⊗[K] L` is a reduced Artinian ring
and hence is canonically the finite product of its residue fields at all
maximal ideals.  This file keeps those literal quotient fields as the
components and aggregates componentwise etaleness of their integral closures
to etaleness of the normalization in their product.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uK uF uL

/-- The algebra structure on a selected generic tensor component obtained
from the canonical left-factor embedding `F → (F ⊗[K] L) / m` and a
specified map `R → F`. -/
@[reducible]
noncomputable def genericTensorFieldComponentLeftScalarAlgebra
    {R : Type uR} {K : Type uK} {F : Type uF} {L : Type uL}
    [CommRing R] [Field K] [Field F] [Field L]
    [Algebra R F] [Algebra K F] [Algebra K L]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    Algebra R (GenericTensorFieldComponent m) :=
  inferInstanceAs (Algebra R ((F ⊗[K] L) ⧸ m))

/-- The algebra structure on the whole generic tensor product induced by
the canonical left factor and a specified map `R → F`. -/
@[reducible]
noncomputable def genericTensorProductLeftScalarAlgebra
    {R : Type uR} {K : Type uK} {F : Type uF} {L : Type uL}
    [CommRing R] [Field K] [Field F] [Field L]
    [Algebra R F] [Algebra K F] [Algebra K L] :
    Algebra R (F ⊗[K] L) :=
  Algebra.TensorProduct.leftAlgebra

/-- The reduced Artinian generic tensor product as the product of its
literal maximal-ideal quotient fields, upgraded to an equivalence over the
original scalar ring `R`. -/
noncomputable def genericTensorProductEquivFieldComponents
    {R : Type uR} {K : Type uK} {F : Type uF} {L : Type uL}
    [CommRing R] [Field K] [Field F] [Field L]
    [Algebra R F] [Algebra K F] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    let G := F ⊗[K] L
    let A := fun M : MaximalSpectrum G =>
      GenericTensorFieldComponent M.asIdeal
    letI : Algebra R G := genericTensorProductLeftScalarAlgebra
    letI : ∀ M, Algebra R (A M) := fun M =>
      genericTensorFieldComponentLeftScalarAlgebra (R := R) M.asIdeal
    G ≃ₐ[R] ∀ M, A M := by
  let G := F ⊗[K] L
  let A := fun M : MaximalSpectrum G =>
    GenericTensorFieldComponent M.asIdeal
  letI : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  letI : Algebra F G := Algebra.TensorProduct.leftAlgebra
  letI : Module.Finite F G := Module.Finite.base_change K F L
  letI : Algebra.Etale F G := by infer_instance
  letI : IsArtinianRing G := isArtinian_of_tower F inferInstance
  letI : IsReduced G :=
    Algebra.FormallyUnramified.isReduced_of_field F G
  letI : Algebra R G := genericTensorProductLeftScalarAlgebra
  letI : ∀ M, Algebra R (A M) := fun M =>
    genericTensorFieldComponentLeftScalarAlgebra (R := R) M.asIdeal
  exact AlgEquiv.ofRingEquiv
    (R := R) (f := (IsArtinianRing.equivPi G).toRingEquiv) fun r => by
      funext M
      rfl

/-- If every literal maximal-ideal component of a finite separable generic
tensor product has etale normalization, then the normalization in the finite
product of all those components is etale.

The index is `MaximalSpectrum (F ⊗[K] L)`, so a previously fixed maximal
ideal remains the same quotient-field component in the conclusion. -/
theorem integralClosure_genericTensorFieldComponents_etale
    {R : Type uR} {K : Type uK} {F : Type uF} {L : Type uL}
    [CommRing R] [Field K] [Field F] [Field L]
    [Algebra R F] [Algebra K F] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hlocal : ∀ (m : Ideal (F ⊗[K] L)) [m.IsMaximal],
      letI : Algebra R (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentLeftScalarAlgebra (R := R) m
      Algebra.Etale R
        (integralClosure R (GenericTensorFieldComponent m))) :
    let G := F ⊗[K] L
    let A := fun M : MaximalSpectrum G =>
      GenericTensorFieldComponent M.asIdeal
    letI : ∀ M, Algebra R (A M) := fun M =>
      genericTensorFieldComponentLeftScalarAlgebra (R := R) M.asIdeal
    Algebra.Etale R (integralClosure R (∀ M, A M)) := by
  let G := F ⊗[K] L
  let A := fun M : MaximalSpectrum G =>
    GenericTensorFieldComponent M.asIdeal
  let : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  let : Algebra F G := Algebra.TensorProduct.leftAlgebra
  let : Module.Finite F G := Module.Finite.base_change K F L
  let : Algebra.Etale F G := by infer_instance
  let : IsArtinianRing G := isArtinian_of_tower F inferInstance
  let : IsReduced G :=
    Algebra.FormallyUnramified.isReduced_of_field F G
  let : ∀ M, Algebra R (A M) := fun M =>
    genericTensorFieldComponentLeftScalarAlgebra (R := R) M.asIdeal
  let : ∀ M, Algebra.Etale R (integralClosure R (A M)) := fun M =>
    hlocal M.asIdeal
  exact integralClosure_pi_etale A

/-- Integral closure transports canonically across the product decomposition
of the finite separable generic tensor product. -/
noncomputable def integralClosureGenericTensorProductEquivComponents
    {R : Type uR} {K : Type uK} {F : Type uF} {L : Type uL}
    [CommRing R] [Field K] [Field F] [Field L]
    [Algebra R F] [Algebra K F] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    let G := F ⊗[K] L
    let A := fun M : MaximalSpectrum G =>
      GenericTensorFieldComponent M.asIdeal
    letI : Algebra R G := genericTensorProductLeftScalarAlgebra
    letI : ∀ M, Algebra R (A M) := fun M =>
      genericTensorFieldComponentLeftScalarAlgebra (R := R) M.asIdeal
    integralClosure R G ≃ₐ[R] integralClosure R (∀ M, A M) := by
  let G := F ⊗[K] L
  let A := fun M : MaximalSpectrum G =>
    GenericTensorFieldComponent M.asIdeal
  letI : Algebra R G := genericTensorProductLeftScalarAlgebra
  letI : ∀ M, Algebra R (A M) := fun M =>
    genericTensorFieldComponentLeftScalarAlgebra (R := R) M.asIdeal
  exact (genericTensorProductEquivFieldComponents
    (R := R) (K := K) (F := F) (L := L)).mapIntegralClosure

/-- Componentwise etaleness of all literal quotient-field normalizations
implies etaleness of the normalization in the original generic tensor
product.  The comparison is the canonical Artinian product decomposition,
not an input hypothesis. -/
theorem integralClosure_genericTensorProduct_etale
    {R : Type uR} {K : Type uK} {F : Type uF} {L : Type uL}
    [CommRing R] [Field K] [Field F] [Field L]
    [Algebra R F] [Algebra K F] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hlocal : ∀ (m : Ideal (F ⊗[K] L)) [m.IsMaximal],
      letI : Algebra R (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentLeftScalarAlgebra (R := R) m
      Algebra.Etale R
        (integralClosure R (GenericTensorFieldComponent m))) :
    let G := F ⊗[K] L
    letI : Algebra R G := genericTensorProductLeftScalarAlgebra
    Algebra.Etale R (integralClosure R G) := by
  let G := F ⊗[K] L
  let A := fun M : MaximalSpectrum G =>
    GenericTensorFieldComponent M.asIdeal
  let : Algebra R G := genericTensorProductLeftScalarAlgebra
  let : ∀ M, Algebra R (A M) := fun M =>
    genericTensorFieldComponentLeftScalarAlgebra (R := R) M.asIdeal
  let : Algebra.Etale R (integralClosure R (∀ M, A M)) :=
    integralClosure_genericTensorFieldComponents_etale hlocal
  let E : integralClosure R G ≃ₐ[R]
      integralClosure R (∀ M, A M) :=
    integralClosureGenericTensorProductEquivComponents
      (R := R) (K := K) (F := F) (L := L)
  exact Algebra.Etale.of_equiv E.symm

end EtaleFundamentalGroups

end
