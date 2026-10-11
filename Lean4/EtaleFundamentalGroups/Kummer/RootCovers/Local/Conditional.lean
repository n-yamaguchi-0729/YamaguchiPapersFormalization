/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.RootCovers.Local.Residue

/-!
# Iterated local root covers with trivial stages

After localizing at a prime, a boundary parameter outside that prime is a
unit.  Such a parameter must not be adjoined with a nontrivial root if one
wants the whole iterated cover to remain local.  The conditional presentation
used at a chosen prime gives those parameters exponent one.  A degree-one
stage is canonically the base ring, so it preserves both locality and the
residue field without requiring its radicand to lie in the maximal ideal.

The local-ring and faithful-flat structures below remain theorem-produced and
are installed only in proof scope.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- A degree-one root-adjunction is canonically the base algebra. -/
def adjoinRootOneAlgEquiv
    {R : Type u} [CommRing R] (a : R) :
    AdjoinRoot (X ^ 1 - C a) ≃ₐ[R] R := by
  refine (AdjoinRoot.algEquivOfEq R (X ^ 1 - C a) (X - C a) ?_).trans ?_
  · simp only [pow_one]
  · change (R[X] ⧸ Ideal.span ({X - C a} : Set R[X])) ≃ₐ[R] R
    exact Polynomial.quotientSpanXSubCAlgEquiv a

/-- The algebra map into a degree-one root-adjunction is bijective. -/
theorem algebraMap_bijective_adjoinRootOne
    {R : Type u} [CommRing R] (a : R) :
    Function.Bijective (algebraMap R (AdjoinRoot (X ^ 1 - C a))) := by
  let e := adjoinRootOneAlgEquiv a
  have he : (e.symm : R → AdjoinRoot (X ^ 1 - C a)) =
      algebraMap R (AdjoinRoot (X ^ 1 - C a)) := by
    funext x
    exact e.symm.commutes x
  rw [← he]
  exact e.symm.bijective

/-- A positive one-step root cover is local when either the radicand is in the
closed point or the root-adjunction is the trivial degree-one stage. -/
theorem isLocalRing_adjoinRoot_X_pow_sub_C_of_mem_or_eq_one
    {R : Type u} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : 0 < n) {a : R}
    (hstage : a ∈ IsLocalRing.maximalIdeal R ∨ n = 1) :
    IsLocalRing (AdjoinRoot (X ^ n - C a)) := by
  rcases hstage with ha | rfl
  · exact isLocalRing_adjoinRoot_X_pow_sub_C hn ha
  · exact (adjoinRootOneAlgEquiv a).symm.toRingEquiv.isLocalRing

private theorem exists_isLocalRing_iteratedRadical_and_map_mem_maximalIdeal_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i, a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    ∃ hlocal : IsLocalRing (iteratedRadical A r n a),
      ∀ x ∈ IsLocalRing.maximalIdeal A,
        algebraMap A (iteratedRadical A r n a) x ∈
          @IsLocalRing.maximalIdeal (iteratedRadical A r n a) _ hlocal := by
  induction r with
  | zero =>
      change ∃ hlocal : IsLocalRing A,
        ∀ x ∈ IsLocalRing.maximalIdeal A,
          algebraMap A A x ∈ @IsLocalRing.maximalIdeal A _ hlocal
      refine ⟨inferInstance, ?_⟩
      intro x hx
      simpa using hx
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      obtain ⟨hT, hmapT⟩ :=
        ih (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc) (fun i ↦ hstage i.castSucc)
      let : IsLocalRing T := hT
      have hstageLast :
          algebraMap A T (a (Fin.last r)) ∈ IsLocalRing.maximalIdeal T ∨
            n (Fin.last r) = 1 := by
        rcases hstage (Fin.last r) with ha | heq
        · exact Or.inl (hmapT _ ha)
        · exact Or.inr heq
      have hB : IsLocalRing (AdjoinRoot f) :=
        isLocalRing_adjoinRoot_X_pow_sub_C_of_mem_or_eq_one
          (hn (Fin.last r)) hstageLast
      refine ⟨hB, ?_⟩
      let : IsLocalRing (AdjoinRoot f) := hB
      let : Module.FaithfullyFlat T (AdjoinRoot f) :=
        faithfullyFlat_adjoinRoot_X_pow_sub_C
          (hn (Fin.last r)) (algebraMap A T (a (Fin.last r)))
      intro x hx
      change algebraMap A (AdjoinRoot f) x ∈
        IsLocalRing.maximalIdeal (AdjoinRoot f)
      rw [IsScalarTower.algebraMap_apply A T (AdjoinRoot f)]
      exact map_nonunit (algebraMap T (AdjoinRoot f)) _ (hmapT x hx)

/-- A positive iterated root cover is local if every stage either adjoins a
root of a closed-point element or has exponent one. -/
theorem isLocalRing_iteratedRadical_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i, a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    IsLocalRing (iteratedRadical A r n a) :=
  (exists_isLocalRing_iteratedRadical_and_map_mem_maximalIdeal_of_mem_or_eq_one
    n a hn hstage).choose

/-- The original closed point maps into the closed point of a conditional
iterated root cover. -/
theorem algebraMap_mem_maximalIdeal_iteratedRadical_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i, a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1)
    [IsLocalRing (iteratedRadical A r n a)]
    {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A) :
    algebraMap A (iteratedRadical A r n a) x ∈
      IsLocalRing.maximalIdeal (iteratedRadical A r n a) := by
  simpa using
    (exists_isLocalRing_iteratedRadical_and_map_mem_maximalIdeal_of_mem_or_eq_one
      n a hn hstage).choose_spec x hx

/-- The residue-field map of a conditional one-step local root cover is
bijective. -/
theorem residueFieldMap_bijective_adjoinRoot_X_pow_sub_C_of_mem_or_eq_one
    {R : Type u} [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : 0 < n) {a : R}
    (hstage : a ∈ IsLocalRing.maximalIdeal R ∨ n = 1) :
    let B := AdjoinRoot (X ^ n - C a)
    letI : IsLocalRing B :=
      isLocalRing_adjoinRoot_X_pow_sub_C_of_mem_or_eq_one hn hstage
    letI : Module.FaithfullyFlat R B :=
      faithfullyFlat_adjoinRoot_X_pow_sub_C hn a
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R B)) := by
  dsimp only
  rcases hstage with ha | hOne
  · simpa using residueFieldMap_bijective_adjoinRoot_X_pow_sub_C hn ha
  · subst n
    let B := AdjoinRoot (X ^ 1 - C a)
    let : IsLocalRing B :=
      isLocalRing_adjoinRoot_X_pow_sub_C_of_mem_or_eq_one Nat.one_pos (Or.inr rfl)
    let : Module.FaithfullyFlat R B :=
      faithfullyFlat_adjoinRoot_X_pow_sub_C Nat.one_pos a
    constructor
    · exact (IsLocalRing.ResidueField.map (algebraMap R B)).injective
    · intro y
      obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨x, rfl⟩ := (algebraMap_bijective_adjoinRootOne a).2 b
      exact ⟨IsLocalRing.residue R x, IsLocalRing.ResidueField.map_residue _ x⟩

/-- A conditional positive iterated local root cover preserves the residue
field. -/
theorem residueFieldMap_bijective_iteratedRadical_of_mem_or_eq_one
    {A : Type u} [CommRing A] [hA : IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i, a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    letI : Module.FaithfullyFlat A B :=
      faithfullyFlat_iteratedRadical n a hn
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B)) := by
  dsimp only
  induction r with
  | zero =>
      simp only [iteratedRadical]
      constructor
      · exact (IsLocalRing.ResidueField.map (algebraMap A A)).injective
      · intro y
        obtain ⟨x, rfl⟩ := @IsLocalRing.residue_surjective A _ hA y
        exact ⟨@IsLocalRing.residue A _ hA x, rfl⟩
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let : IsLocalRing T :=
        isLocalRing_iteratedRadical_of_mem_or_eq_one
          (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc) (fun i ↦ hstage i.castSucc)
      let : Module.FaithfullyFlat A T :=
        faithfullyFlat_iteratedRadical
          (Fin.init n) (Fin.init a) (fun i ↦ hn i.castSucc)
      have hstageLast :
          algebraMap A T (a (Fin.last r)) ∈ IsLocalRing.maximalIdeal T ∨
            n (Fin.last r) = 1 := by
        rcases hstage (Fin.last r) with ha | heq
        · exact Or.inl
            (algebraMap_mem_maximalIdeal_iteratedRadical_of_mem_or_eq_one
              (Fin.init n) (Fin.init a)
              (fun i ↦ hn i.castSucc) (fun i ↦ hstage i.castSucc) ha)
        · exact Or.inr heq
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      let B := AdjoinRoot f
      let : IsLocalRing B :=
        isLocalRing_adjoinRoot_X_pow_sub_C_of_mem_or_eq_one
          (hn (Fin.last r)) hstageLast
      let : Module.FaithfullyFlat T B :=
        faithfullyFlat_adjoinRoot_X_pow_sub_C
          (hn (Fin.last r)) (algebraMap A T (a (Fin.last r)))
      let : Module.FaithfullyFlat A B :=
        Module.FaithfullyFlat.trans A T B
      have hinit : Function.Bijective
          (IsLocalRing.ResidueField.map (algebraMap A T)) :=
        ih (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc) (fun i ↦ hstage i.castSucc)
      have hlast : Function.Bijective
          (IsLocalRing.ResidueField.map (algebraMap T B)) :=
        residueFieldMap_bijective_adjoinRoot_X_pow_sub_C_of_mem_or_eq_one
          (hn (Fin.last r)) hstageLast
      change Function.Bijective
        (IsLocalRing.ResidueField.map (algebraMap A B))
      constructor
      · exact (IsLocalRing.ResidueField.map (algebraMap A B)).injective
      · intro z
        obtain ⟨y, hy⟩ := hlast.2 z
        obtain ⟨x, hx⟩ := hinit.2 y
        refine ⟨x, ?_⟩
        obtain ⟨x₀, rfl⟩ := IsLocalRing.residue_surjective x
        calc
          IsLocalRing.ResidueField.map (algebraMap A B)
              (IsLocalRing.residue A x₀) =
              IsLocalRing.ResidueField.map (algebraMap T B)
                (IsLocalRing.ResidueField.map (algebraMap A T)
                  (IsLocalRing.residue A x₀)) := by
            rw [IsLocalRing.ResidueField.map_residue,
              IsLocalRing.ResidueField.map_residue,
              IsLocalRing.ResidueField.map_residue,
              IsScalarTower.algebraMap_apply A T B]
          _ = IsLocalRing.ResidueField.map (algebraMap T B) y := by rw [hx]
          _ = z := hy

end EtaleFundamentalGroups.Kummer

end
