/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.DominantPreimmersionPullback
import SchemeTheory.FiniteEtale.DensePullback

/-!
# Automorphisms of the generic pullback of a Galois cover

Pullback to the generic point preserves the full deck-transformation group
of a finite-etale Galois cover over a normal integral locally Noetherian
scheme.
-/

noncomputable section

open CategoryTheory Limits MorphismProperty
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

private theorem genericExtensionMorphism_self_isDominant
    (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (X.genericExtensionMorphism X.functionField) := by
  constructor
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec X).def]
  apply closure_mono
  intro x hx
  rcases hx with rfl
  rw [Set.mem_range]
  exact ⟨IsLocalRing.closedPoint X.functionField,
    X.genericExtensionMorphism_apply_closedPoint X.functionField⟩

private theorem genericExtensionMorphism_self_isPreimmersion
    (X : Scheme.{u}) [IsIntegral X] :
    IsPreimmersion (X.genericExtensionMorphism X.functionField) := by
  rw [Scheme.genericExtensionMorphism]
  let : IsPreimmersion
      (Spec.map (CommRingCat.ofHom
        (algebraMap X.functionField X.functionField))) := by
    have h : CommRingCat.ofHom
        (algebraMap X.functionField X.functionField) =
        𝟙 (CommRingCat.of X.functionField) := by
      ext x
      simp
    rw [h]
    infer_instance
  infer_instance

/-- Pullback to the generic point induces the canonical multiplicative
equivalence from global deck transformations to generic deck
transformations. -/
noncomputable def finiteEtaleAutGenericPullbackMulEquiv
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Z : FiniteEtale X) (hZ : IsGalois Z) :
    let eta := X.genericExtensionMorphism X.functionField
    Aut Z ≃* Aut ((FiniteEtale.pullback eta).obj Z) := by
  let eta := X.genericExtensionMorphism X.functionField
  letI : IsDominant eta := genericExtensionMorphism_self_isDominant X
  letI : IsPreimmersion eta := genericExtensionMorphism_self_isPreimmersion X
  letI : IsGalois Z := hZ
  let P : FiniteEtale (Spec (.of X.functionField)) :=
    (FiniteEtale.pullback eta).obj Z
  have hP : IsGalois P :=
    FiniteEtale.pullback_obj_isGalois_of_isPreimmersion_of_isDominant
      eta Z hZ
  letI : IsGalois P := hP
  letI : IsSchemeTheoreticallyDominant eta :=
    IsSchemeTheoreticallyDominant.of_isDominant eta
  let F := FiniteEtale.pullback eta
  letI : F.Faithful := AlgebraicGeometry.FiniteEtale.pullback_faithful_of_isDominant eta
  have hAutInj : Function.Injective (F.mapAut Z) := by
    intro sigma tau h
    apply Aut.ext
    apply F.map_injective
    exact congrArg Iso.hom h
  let x : Spec (.of X.functionField) := Classical.choice inferInstance
  let Omega := AlgebraicClosure ((Spec (.of X.functionField)).residueField x)
  let xi : Spec (.of Omega) ⟶ Spec (.of X.functionField) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap ((Spec (.of X.functionField)).residueField x) Omega)) ≫
      (Spec (.of X.functionField)).fromSpecResidueField x
  let xOmega := IsLocalRing.closedPoint Omega
  have hZcard : Nat.card (Aut Z) =
      Z.hom.finrank ((xi ≫ eta) xOmega) :=
    (FiniteEtale.isGalois_iff_card_aut_eq_finrank (xi ≫ eta) Z).mp hZ
  have hPcard : Nat.card (Aut P) = P.hom.finrank (xi xOmega) :=
    (FiniteEtale.isGalois_iff_card_aut_eq_finrank xi P).mp hP
  have hrank : P.hom.finrank (xi xOmega) =
      Z.hom.finrank ((xi ≫ eta) xOmega) := by
    change (pullback.snd Z.hom eta).finrank (xi xOmega) =
      Z.hom.finrank (eta (xi xOmega))
    have hpb : IsPullback
        (pullback.fst Z.hom eta) (pullback.snd Z.hom eta) Z.hom eta :=
      IsPullback.of_hasPullback Z.hom eta
    exact Scheme.Hom.finrank_of_isPullback
      (pullback.fst Z.hom eta) (pullback.snd Z.hom eta)
      Z.hom eta hpb (xi xOmega)
  have hcard : Nat.card (Aut Z) = Nat.card (Aut P) := by
    calc
      Nat.card (Aut Z) = Z.hom.finrank ((xi ≫ eta) xOmega) := hZcard
      _ = P.hom.finrank (xi xOmega) := hrank.symm
      _ = Nat.card (Aut P) := hPcard.symm
  exact MulEquiv.ofBijective (F.mapAut Z)
    ((Nat.bijective_iff_injective_and_card (F.mapAut Z)).mpr
      ⟨hAutInj, hcard⟩)

@[simp]
theorem finiteEtaleAutGenericPullbackMulEquiv_apply
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Z : FiniteEtale X) (hZ : IsGalois Z) (sigma : Aut Z) :
    finiteEtaleAutGenericPullbackMulEquiv Z hZ sigma =
      (FiniteEtale.pullback
        (X.genericExtensionMorphism X.functionField)).mapIso sigma := by
  rfl

end EtaleFundamentalGroups

end
