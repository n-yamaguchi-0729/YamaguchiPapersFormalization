/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.IteratedRadical.Basic
import EtaleFundamentalGroups.Kummer.RootCovers.Local.Basic

/-!
# Locality of finite iterated Kummer root covers

If every radicand belongs to the closed point of a local base ring, adjoining positive roots of
those radicands one after another stays local.  The proof also keeps track of the closed point:
the image of the original maximal ideal remains inside the maximal ideal at every stage.

The resulting `IsLocalRing` proofs are theorems, not global recursive instances.  Consumers install
one proof locally when needed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

private theorem exists_isLocalRing_iteratedRadical_and_map_mem_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
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
          (fun i ↦ hn i.castSucc) (fun i ↦ ha i.castSucc)
      let : IsLocalRing T := hT
      have haLast :
          algebraMap A T (a (Fin.last r)) ∈ IsLocalRing.maximalIdeal T :=
        hmapT (a (Fin.last r)) (ha (Fin.last r))
      have hB : IsLocalRing (AdjoinRoot f) :=
        isLocalRing_adjoinRoot_X_pow_sub_C (hn (Fin.last r)) haLast
      refine ⟨hB, ?_⟩
      let : IsLocalRing (AdjoinRoot f) := hB
      intro x hx
      change algebraMap A (AdjoinRoot f) x ∈ IsLocalRing.maximalIdeal (AdjoinRoot f)
      rw [maximalIdeal_adjoinRoot_X_pow_sub_C (hn (Fin.last r)) haLast]
      refine (show Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal T) ≤
        localRootCoverClosedIdeal T (n (Fin.last r))
          (algebraMap A T (a (Fin.last r))) from le_sup_left) ?_
      have hxT : algebraMap A T x ∈ IsLocalRing.maximalIdeal T := hmapT x hx
      have hmem :
          AdjoinRoot.of f (algebraMap A T x) ∈
            Ideal.map (AdjoinRoot.of f) (IsLocalRing.maximalIdeal T) :=
        Ideal.mem_map_of_mem (AdjoinRoot.of f) hxT
      simpa [IsScalarTower.algebraMap_apply A T (AdjoinRoot f)] using hmem

/-- A finite iterated positive Kummer root cover of closed-point elements is local. -/
theorem isLocalRing_iteratedRadical
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing (iteratedRadical A r n a) :=
  (exists_isLocalRing_iteratedRadical_and_map_mem_maximalIdeal n a hn ha).choose

/-- Under the locally supplied structure, the original closed point maps into the closed point of
the finite iterated root cover. -/
theorem algebraMap_mem_maximalIdeal_iteratedRadical
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A)
    [IsLocalRing (iteratedRadical A r n a)]
    {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A) :
    algebraMap A (iteratedRadical A r n a) x ∈
      IsLocalRing.maximalIdeal (iteratedRadical A r n a) := by
  simpa using
    (exists_isLocalRing_iteratedRadical_and_map_mem_maximalIdeal n a hn ha).choose_spec x hx

end EtaleFundamentalGroups.Kummer

end
