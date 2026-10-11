/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.Finite
import SchemeTheory.FiniteEtale.Away.TensorBaseChange
import EtaleFundamentalGroups.Completions.FiniteEtale.ClosedPrime
import SchemeTheory.FiniteEtale.Henselian.ChosenLocalizationEtale
import EtaleFundamentalGroups.Normalization.IntegralClosure.IntegralBase.ChosenLocalization.Core

/-!
# Boundary Away at the same prime after maximal-adic completion

Let `p` be a chosen closed prime in a finite etale algebra `E / R`.  After
maximal-adic completion put

`T = Rhat ⊗[R] E` and `pHat = p.map (algebraMap E T)`.

Completion may split a non-Henselian local factor, so in general one must not
identify `Rhat ⊗[R] E_p` with the whole ring `T_pHat`.  What is true, and
what the boundary argument needs, is the following weaker statement.

* `pHat` contracts literally to `p`;
* `Rhat ⊗[R] E_p` is the localization of `T` at the image of `pᶜ`;
* `T_pHat` is a further localization of that tensor product;
* the chosen localization is finite over the complete Henselian base.

Consequently a literal etale Away map on `E_p` base-changes and then extends
to the localization at the same mapped prime `pHat`.  No tensor/local-factor
equivalence and no independently selected completed prime is used.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uE

/-- The etaleness predicate for a literal Away map, named so dependent
completion targets do not force the elaborator to reconstruct their
localized commutative-ring structures in a theorem signature. -/
private abbrev localizationAwayMapEtale
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : R) : Prop :=
  (Localization.awayMap (algebraMap R S) f).Etale

/-- Localizing an étale algebra map at a source element remains étale. -/
private theorem localizationAwayMapEtale_of_etale
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (f : R) :
    localizationAwayMapEtale (R := R) (S := S) f := by
  let fS : S := algebraMap R S f
  let U := Localization.Away f
  let V := Localization.Away fS
  let mapUV : U →+* V := Localization.awayMap (algebraMap R S) f
  let : Algebra U V := mapUV.toAlgebra
  let : IsScalarTower R S V := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R U V := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap R V r = mapUV (algebraMap R U r)
    rw [IsScalarTower.algebraMap_apply R S V]
    simp [mapUV, U, V, fS, IsLocalization.Away.map]
  let : Algebra.Etale R U := Algebra.Etale.of_isLocalizationAway f
  exact (show Algebra.Etale U V from Algebra.Etale.of_restrictScalars R U V)

/-- The exact mapped prime in a completion tensor product contracts to the
original prime.  This is faithful-flat contraction, not a choice of a prime
above `p`. -/
theorem adicCompletion_finiteEtale_mappedPrime_comap
    {R : Type uR} {E : Type uE}
    [CommRing R] [CommRing E]
    [IsNoetherianRing R] [IsLocalRing R]
    [Algebra R E]
    (p : Ideal E) :
    let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let T := Rhat ⊗[R] E
    letI : Algebra E T := Algebra.TensorProduct.rightAlgebra
    let pHat := p.map (algebraMap E T)
    pHat.comap (algebraMap E T) = p := by
  dsimp only
  let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let T := Rhat ⊗[R] E
  let : Module.FaithfullyFlat R Rhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let : Module.FaithfullyFlat E T :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := E) (M := E ⊗[R] Rhat)
      (Algebra.TensorProduct.commRight R E Rhat).symm.toLinearEquiv
  exact Ideal.comap_map_eq_self_of_faithfullyFlat
    (A := E) (B := T) p

universe uA uB uA' uB'

/-- Application-shaped same-prime transport with distinct boundary and
finite-etale bases.

Here `A → B` is the (possibly ramified) finite radical cover, `A'` is the
completed boundary base, and `B'` is its finite Henselian base change.  The
square `A-B-A'-B'` is a pushout.  The algebra `E` is finite etale over `B`,
not over `A`.

The hypotheses `hmax` and `hres` say that `B → B'` preserves the selected
closed fibre.  They produce the exact maximal ideal
`p' = p.map (algebraMap E (B' ⊗[B] E))`.  The input Away map is nevertheless
over `A`; pushout pasting first base-changes it to
`B' ⊗[B] E_p`.  The latter maps to the localization at `p'` as a further
localization.  Finiteness is obtained first over `B'` by Henselian
finite-etale localization and then over `A'` by the finite tower.

Thus neither ramification of `B/A` nor splitting of a non-Henselian local
factor forces a false tensor/localization equivalence. -/
theorem finiteEtale_samePrime_boundaryAway_of_finite_henselianPushout
    {A : Type uA} {B : Type uB}
    {A' : Type uA'} {B' : Type uB'} {E : Type uE}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing E]
    [IsNoetherianRing A']
    [IsLocalRing B] [HenselianLocalRing B']
    [Algebra A B] [Algebra A A'] [Algebra A B']
    [Algebra B B'] [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    [Algebra.IsPushout A B A' B']
    [IsLocalHom (algebraMap B B')]
    [Module.FaithfullyFlat B B']
    [Module.Finite A B]
    [Algebra B E] [Algebra A E] [IsScalarTower A B E]
    [Module.Finite B E] [Algebra.Etale B E]
    (p : Ideal E) [p.IsMaximal]
    [p.LiesOver (IsLocalRing.maximalIdeal B)]
    (hmax : (IsLocalRing.maximalIdeal B).map (algebraMap B B') =
      IsLocalRing.maximalIdeal B')
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap B B')))
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (Localization.AtPrime p)) f).Etale) :
    let T := B' ⊗[B] E
    letI : Algebra B' T := Algebra.TensorProduct.leftAlgebra
    letI : Algebra E T := Algebra.TensorProduct.rightAlgebra
    let p' := p.map (algebraMap E T)
    let hp' : p'.IsMaximal :=
      (tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
        (R := B) (R' := B') (S := E) p hmax hres).1
    letI : p'.IsPrime := hp'.isPrime
    let hp'Over : p'.LiesOver (IsLocalRing.maximalIdeal B') :=
      (tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
        (R := B) (R' := B') (S := E) p hmax hres).2
    letI : p'.LiesOver (IsLocalRing.maximalIdeal B') := hp'Over
    let D := Localization.AtPrime p'
    letI : Algebra B' D :=
      ((algebraMap T D).comp (algebraMap B' T)).toAlgebra
    letI : Algebra A' D :=
      ((algebraMap B' D).comp (algebraMap A' B')).toAlgebra
    localizationAwayMapEtale (R := A') (S := D)
      (algebraMap A A' f) := by
  dsimp only
  let T := B' ⊗[B] E
  let : Algebra B' T := Algebra.TensorProduct.leftAlgebra
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B B' T := inferInstance
  let : IsScalarTower B E T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Module.FaithfullyFlat E T :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := E) (M := E ⊗[B] B')
      (Algebra.TensorProduct.commRight B E B').symm.toLinearEquiv
  let : Algebra.IsPushout A A' B B' :=
    (inferInstance : Algebra.IsPushout A B A' B').symm
  let : Module.Finite A' (A' ⊗[A] B) :=
    Module.Finite.base_change A A' B
  let : Module.Finite A' B' :=
    Module.Finite.equiv
      (Algebra.IsPushout.equiv A A' B B').toLinearEquiv
  let p' := p.map (algebraMap E T)
  have hgeometry :=
    tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R := B) (R' := B') (S := E) p hmax hres
  let : p'.IsPrime := hgeometry.1.isPrime
  let : p'.LiesOver (IsLocalRing.maximalIdeal B') := hgeometry.2
  let D := Localization.AtPrime p'
  let : Algebra T D := inferInstance
  let : IsScalarTower B' T D :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hTowerABaseD : IsScalarTower A' B' D :=
    IsScalarTower.of_algebraMap_eq' rfl
  let Ep := Localization.AtPrime p
  let C := B' ⊗[B] Ep
  let : Algebra B' C := Algebra.TensorProduct.leftAlgebra
  let : Algebra Ep C := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B B' C := inferInstance
  let : IsScalarTower B Ep C :=
    Algebra.TensorProduct.right_isScalarTower
  let : Algebra A' C := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower A' B' C :=
    TensorProduct.isScalarTower_left
  let : Algebra A C := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower A A' C :=
    TensorProduct.isScalarTower_left
  let : IsScalarTower A B' C :=
    IsScalarTower.to₁₃₄ A A' B' C
  let : IsScalarTower A B C :=
    IsScalarTower.to₁₂₄ A B B' C
  let : IsScalarTower A E Ep := inferInstance
  let : IsScalarTower A B Ep :=
    IsScalarTower.to₁₂₄ A B E Ep
  let : IsScalarTower A Ep C :=
    IsScalarTower.to₁₃₄ A B Ep C
  have hSecondPushout : Algebra.IsPushout B Ep B' C :=
    (inferInstance : Algebra.IsPushout B B' Ep C).symm
  have hTotalPushout : Algebra.IsPushout A Ep A' C :=
    (Algebra.IsPushout.comp_iff A B A' B').2 hSecondPushout
  let : Algebra.IsPushout A Ep A' C := hTotalPushout
  have hAwayBaseChange : localizationAwayMapEtale
      (R := A') (S := C) (algebraMap A A' f) :=
    localization_awayMap_etale_of_isPushout
      (A := A) (B := Ep) (C := A') (D := C) f hAway
  let mapTC : T →ₐ[B] C :=
    Algebra.TensorProduct.map (AlgHom.id B B')
      (IsScalarTower.toAlgHom B E Ep)
  let : Algebra T C := mapTC.toAlgebra
  let : IsScalarTower B' T C :=
    IsScalarTower.of_algebraMap_eq <| by
      intro x
      change x ⊗ₜ[B] (1 : Ep) = mapTC (x ⊗ₜ[B] (1 : E))
      rw [show mapTC (x ⊗ₜ[B] (1 : E)) =
          (AlgHom.id B B') x ⊗ₜ[B]
            (IsScalarTower.toAlgHom B E Ep) 1 from
        Algebra.TensorProduct.map_tmul
          (AlgHom.id B B') (IsScalarTower.toAlgHom B E Ep) x 1]
      simp only [AlgHom.id_apply, map_one]
  let M : Submonoid T :=
    p.primeCompl.map
      (Algebra.TensorProduct.includeRight (R := B) (A := B') (B := E))
  let N : Submonoid T := p'.primeCompl
  let : IsLocalization M C := by
    exact
      IsLocalization.tensorProduct_tensorProduct_right
        B B' p.primeCompl Ep (by
          ext x
          change mapTC (1 ⊗ₜ[B] x) =
            1 ⊗ₜ[B] algebraMap E Ep x
          rw [show mapTC (1 ⊗ₜ[B] x) =
              (AlgHom.id B B') 1 ⊗ₜ[B]
                (IsScalarTower.toAlgHom B E Ep) x from
            Algebra.TensorProduct.map_tmul
              (AlgHom.id B B') (IsScalarTower.toAlgHom B E Ep) 1 x]
          simp only [map_one, IsScalarTower.toAlgHom_apply])
  have hp'Comap : p'.comap (algebraMap E T) = p :=
    Ideal.comap_map_eq_self_of_faithfullyFlat
      (A := E) (B := T) p
  have hMN : M ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    change algebraMap E T x ∉ p'
    intro hx'
    apply hx
    rw [← hp'Comap]
    exact hx'
  let cdAlgebra : Algebra C D :=
    IsLocalization.localizationAlgebraOfSubmonoidLe C D M N hMN
  let : Algebra C D := cdAlgebra
  let : IsScalarTower T C D :=
    IsLocalization.localization_isScalarTower_of_submonoid_le C D M N hMN
  let : IsScalarTower B' C D :=
    IsScalarTower.to₁₃₄ B' T C D
  let : IsScalarTower A' C D :=
    IsScalarTower.to₁₃₄ A' B' C D
  let : IsLocalization (N.map (algebraMap T C)) D :=
    IsLocalization.isLocalization_of_submonoid_le C D M N hMN
  let : Algebra.FormallyEtale C D :=
    Algebra.FormallyEtale.of_isLocalization
      (N.map (algebraMap T C))
  let : Module.Finite B' D :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale p'
  have hFiniteABaseD : Module.Finite A' D :=
    @Module.Finite.trans A' B' D _ _ _ _ _ _ hTowerABaseD
      inferInstance inferInstance
  let : Module.Finite A' D := hFiniteABaseD
  exact
    localization_awayMap_etale_of_finite_formallyEtale_extension
      (A := A') (C := C) (D := D)
      (algebraMap A A' f) hAwayBaseChange

/-- A primitive boundary Away map at `p` remains etale at the exact mapped
prime after maximal-adic completion.

The intermediate tensor `Rhat ⊗[R] E_p` is used only as a base change of
the input map.  Its natural map to `T_pHat` is a localization, not asserted
to be an equivalence.  Finiteness of `T_pHat / Rhat` follows from Henselian
finite-etale localization and supplies the finite-presentation part of the
terminal Away map. -/
theorem adicCompletion_finiteEtale_samePrime_boundaryAway
    {R : Type uR} {E : Type uE}
    [CommRing R] [CommRing E]
    [IsNoetherianRing R] [IsLocalRing R]
    [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
    (p : Ideal E) [p.IsMaximal]
    [p.LiesOver (IsLocalRing.maximalIdeal R)]
    (f : R) :
    let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let T := Rhat ⊗[R] E
    letI : Algebra Rhat T := Algebra.TensorProduct.leftAlgebra
    letI : Algebra E T := Algebra.TensorProduct.rightAlgebra
    let pHat := p.map (algebraMap E T)
    let hpHat : pHat.IsMaximal :=
      (adicCompletion_finiteEtale_closedPrime (R := R) (S := E) p).1
    letI : pHat.IsPrime := hpHat.isPrime
    let hpHatOver : pHat.LiesOver (IsLocalRing.maximalIdeal Rhat) :=
      (adicCompletion_finiteEtale_closedPrime (R := R) (S := E) p).2.1
    letI : pHat.LiesOver (IsLocalRing.maximalIdeal Rhat) := hpHatOver
    let D := Localization.AtPrime pHat
    letI : Algebra Rhat D :=
      ((algebraMap T D).comp (algebraMap Rhat T)).toAlgebra
    localizationAwayMapEtale (R := Rhat) (S := D)
      (algebraMap R Rhat f) := by
  dsimp only
  let Rhat := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let T := Rhat ⊗[R] E
  let : Algebra Rhat T := Algebra.TensorProduct.leftAlgebra
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let pHat := p.map (algebraMap E T)
  have hgeometry :=
    adicCompletion_finiteEtale_closedPrime (R := R) (S := E) p
  let : pHat.IsPrime := hgeometry.1.isPrime
  let : pHat.LiesOver (IsLocalRing.maximalIdeal Rhat) :=
    hgeometry.2.1
  let D := Localization.AtPrime pHat
  let canonicalRhatD : Algebra Rhat D := inferInstance
  let : HenselianLocalRing Rhat :=
    { is_henselian := fun g hg x hx hderivative ↦ by
        apply HenselianRing.is_henselian g hg x hx
        exact hderivative.map
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal Rhat)) }
  let : Algebra.Etale Rhat T := hgeometry.2.2.2
  have hCanonicalEtale :
      @Algebra.Etale Rhat D _ _ canonicalRhatD :=
    etale_localizationAtPrime_of_henselian_of_etale pHat
  let compositeRhatD : Algebra Rhat D :=
    ((algebraMap T D).comp (algebraMap Rhat T)).toAlgebra
  have hTower : @IsScalarTower Rhat T D
      (inferInstance : Algebra Rhat T).toSMul
      (inferInstance : Algebra T D).toSMul
      canonicalRhatD.toSMul := by
    let : Algebra Rhat D := canonicalRhatD
    infer_instance
  have hAlgebra : canonicalRhatD = compositeRhatD := by
    apply Algebra.algebra_ext
    intro x
    exact @IsScalarTower.algebraMap_apply Rhat T D _ _ _
      (inferInstance : Algebra Rhat T)
      (inferInstance : Algebra T D) canonicalRhatD hTower x
  have hCompositeEtale :
      @Algebra.Etale Rhat D _ _ compositeRhatD :=
    hAlgebra ▸ hCanonicalEtale
  let : Algebra Rhat D := compositeRhatD
  let : Algebra.Etale Rhat D := hCompositeEtale
  exact localizationAwayMapEtale_of_etale
    (R := Rhat) (S := D) (algebraMap R Rhat f)

end EtaleFundamentalGroups

end
