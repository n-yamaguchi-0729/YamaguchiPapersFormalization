/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CompletionFormalComparison
import Nyll.SchemeTheory.FiniteEtale.Algebra.NilpotentBaseChange
import Nyll.EtaleFundamentalGroups.Purity.FiniteEtaleQuotientBaseChange
import Nyll.EtaleFundamentalGroups.Purity.Local.IdealAdicComplete
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite

/-!
# Finite-etale base change from an adically complete ring

Finite modules over a Noetherian adically complete ring are complete.  Hence
formal etaleness makes reduction modulo the extended ideal bijective on maps.
The tensor-product description of quotient base change then gives full
faithfulness for finite-etale algebras.  For the maximal ideal of a complete
Noetherian local ring, the existing lifting theorem also gives essential
surjectivity, and therefore an equivalence of finite-etale categories.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- If the Noetherian base is complete along an ideal, scalar extension to
the quotient is bijective on maps out of a formally etale algebra and into a
finite algebra. -/
theorem finiteEtale_baseChange_algHom_bijective_of_isAdicComplete
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A]
    [IsNoetherianRing R] [Module.Finite R B]
    (I : Ideal R) [IsAdicComplete I R] :
    Function.Bijective
      (fun f : A →ₐ[R] B ↦
        Algebra.TensorProduct.map (.id (R ⧸ I) (R ⧸ I)) f) := by
  let J : Ideal B := I.map (algebraMap R B)
  have hcomplete : IsAdicComplete I B :=
    ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite
      (I := I) (M := B)
  have hcompleteJ : IsAdicComplete J B :=
    (IsAdicComplete.map_algebraMap_iff (I := I) (M := B) (S := B)).2
      hcomplete
  let : IsAdicComplete J B := hcompleteJ
  apply baseChange_algHom_bijective_of_quotient_comp_bijective I
  exact Algebra.FormallyEtale.comp_bijective_of_isAdicComplete J

/-- Finite-etale base change from a Noetherian adically complete ring to the
corresponding quotient is fully faithful. -/
noncomputable def finiteEtale_baseChange_fullyFaithful_of_isAdicComplete
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] :
    (CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)).FullyFaithful where
  preimage {A B} f :=
    CommAlgCat.FiniteEtale.ofHom <|
      Classical.choose
        ((finiteEtale_baseChange_algHom_bijective_of_isAdicComplete
          (A := A.obj) (B := B.obj) I).2 f.hom.hom)
  map_preimage {A B} f := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.Hom.ext
    exact Classical.choose_spec
      ((finiteEtale_baseChange_algHom_bijective_of_isAdicComplete
        (A := A.obj) (B := B.obj) I).2 f.hom.hom)
  preimage_map {A B} f := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.Hom.ext
    exact
      (finiteEtale_baseChange_algHom_bijective_of_isAdicComplete
        (A := A.obj) (B := B.obj) I).1 <|
        Classical.choose_spec
          ((finiteEtale_baseChange_algHom_bijective_of_isAdicComplete
            (A := A.obj) (B := B.obj) I).2
            ((CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)).map f).hom.hom)

/-- For an ideal in the maximal ideal of a complete Noetherian local ring,
adic completeness along that ideal makes quotient base change an equivalence
on finite-etale algebras. -/
theorem finiteEtale_baseChange_isEquivalence_of_isAdicComplete
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) [IsAdicComplete I R] (hI : I ≤ maximalIdeal R) :
    (CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)).IsEquivalence := by
  let F := CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)
  let hff : F.FullyFaithful :=
    finiteEtale_baseChange_fullyFaithful_of_isAdicComplete I
  let hes : F.EssSurj := finiteEtale_baseChange_essSurj_of_quotient I hI
  exact
    { faithful := hff.faithful
      full := hff.full
      essSurj := hes }

/-- The finite-etale categorical equivalence induced by quotienting a
complete Noetherian local ring by an ideal along which it is complete. -/
noncomputable def finiteEtale_baseChange_equivalence_of_isAdicComplete
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) [IsAdicComplete I R] (hI : I ≤ maximalIdeal R) :
    CommAlgCat.FiniteEtale.{u} R ≌ CommAlgCat.FiniteEtale.{u} (R ⧸ I) := by
  let F := CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)
  letI : F.IsEquivalence :=
    finiteEtale_baseChange_isEquivalence_of_isAdicComplete I hI
  exact F.asEquivalence

/-- Quotient base change by any ideal in the maximal ideal of a complete
Noetherian local ring is an equivalence on finite-etale algebras. -/
theorem finiteEtale_baseChange_isEquivalence_of_le_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    (CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)).IsEquivalence := by
  let : IsAdicComplete I R :=
    Purity.isAdicComplete_of_le_maximalIdeal (M := R) I hI
  exact finiteEtale_baseChange_isEquivalence_of_isAdicComplete I hI

/-- The finite-etale categorical equivalence induced by any quotient of a
complete Noetherian local ring by an ideal in its maximal ideal. -/
noncomputable def finiteEtale_baseChange_equivalence_of_le_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) :
    CommAlgCat.FiniteEtale.{u} R ≌ CommAlgCat.FiniteEtale.{u} (R ⧸ I) := by
  let F := CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ I)
  letI : F.IsEquivalence :=
    finiteEtale_baseChange_isEquivalence_of_le_maximalIdeal I hI
  exact F.asEquivalence

/-- Reduction to the residue quotient of a complete Noetherian local ring is
an equivalence on finite-etale algebras. -/
theorem finiteEtale_baseChange_isEquivalence_quotient_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] :
    (CommAlgCat.FiniteEtale.baseChange.{u} R
      (R ⧸ maximalIdeal R)).IsEquivalence := by
  exact finiteEtale_baseChange_isEquivalence_of_le_maximalIdeal
    (maximalIdeal R) le_rfl

/-- The finite-etale categorical equivalence induced by reduction to the
residue quotient of a complete Noetherian local ring. -/
noncomputable def finiteEtale_baseChange_equivalence_quotient_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] :
    CommAlgCat.FiniteEtale.{u} R ≌
      CommAlgCat.FiniteEtale.{u} (R ⧸ maximalIdeal R) := by
  let F := CommAlgCat.FiniteEtale.baseChange.{u} R (R ⧸ maximalIdeal R)
  letI : F.IsEquivalence :=
    finiteEtale_baseChange_isEquivalence_quotient_maximalIdeal
  exact F.asEquivalence

end EtaleFundamentalGroups

end
