/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyRadical
import Mathlib.RingTheory.Filtration

/-!
# Simultaneous ideal powers and derived local cohomology

The ideal-quotient Mayer--Vietoris diagram uses `I ^ n ⊓ J ^ n` and
`I ^ n ⊔ J ^ n`, whereas local cohomology is defined from powers of a
single ideal.  The supremum comparison is elementary.  For intersections,
Artin--Rees shows that the simultaneous-power filtration is cofinal with
the powers of `I ⊓ J`.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

variable {R : Type u} [CommRing R]

/-- The diagram of simultaneous intersections of powers. -/
def idealInfPowersDiagram (I J : Ideal R) : ℕᵒᵖ ⥤ Ideal R where
  obj n := I ^ unop n ⊓ J ^ unop n
  map f := ⟨⟨inf_le_inf
    (Ideal.pow_le_pow_right f.unop.down.down)
    (Ideal.pow_le_pow_right f.unop.down.down)⟩⟩

/-- The diagram of simultaneous suprema of powers. -/
def idealSupPowersDiagram (I J : Ideal R) : ℕᵒᵖ ⥤ Ideal R where
  obj n := I ^ unop n ⊔ J ^ unop n
  map f := ⟨⟨sup_le_sup
    (Ideal.pow_le_pow_right f.unop.down.down)
    (Ideal.pow_le_pow_right f.unop.down.down)⟩⟩

/-- Artin--Rees makes the simultaneous intersections of powers cofinal with
the powers of the intersection. -/
theorem exists_inf_pow_le_inf_pow (I J : Ideal R) [IsNoetherianRing R]
    (m : ℕ) : ∃ n : ℕ, I ^ n ⊓ J ^ n ≤ (I ⊓ J) ^ m := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (J ^ m)
  let n := k + m
  refine ⟨n, ?_⟩
  have hnmk : n - k = m := by
    dsimp only [n]
    omega
  have hAR := hk n (by
    dsimp only [n]
    omega)
  have hJn : J ^ n ≤ J ^ m :=
    Ideal.pow_le_pow_right (by
      dsimp only [n]
      omega)
  calc
    I ^ n ⊓ J ^ n ≤ I ^ n ⊓ J ^ m := inf_le_inf le_rfl hJn
    _ = I ^ (n - k) * (I ^ k ⊓ J ^ m) := by
      simpa only [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] using hAR
    _ ≤ I ^ m * J ^ m := by
      rw [hnmk]
      exact mul_le_mul' le_rfl inf_le_right
    _ = (I * J) ^ m := (mul_pow I J m).symm
    _ ≤ (I ⊓ J) ^ m := by
      exact pow_le_pow_left' Ideal.mul_le_inf m

section Noetherian

variable [IsNoetherianRing R]

/-- Lift simultaneous intersection powers to the full support category. -/
def idealInfPowersToSelfLERadical (I J : Ideal R) :
    ℕᵒᵖ ⥤ localCohomology.SelfLERadical (I ⊓ J) :=
  ObjectProperty.lift _ (idealInfPowersDiagram I J) fun n => by
    intro x hx
    rw [Ideal.mem_radical_iff]
    exact ⟨unop n,
      ⟨Ideal.pow_mem_pow hx.1 (unop n),
        Ideal.pow_mem_pow hx.2 (unop n)⟩⟩

/-- Lift simultaneous supremum powers to the full support category. -/
def idealSupPowersToSelfLERadical (I J : Ideal R) :
    ℕᵒᵖ ⥤ localCohomology.SelfLERadical (I ⊔ J) :=
  ObjectProperty.lift _ (idealSupPowersDiagram I J) fun n => by
    apply sup_le
    · intro x hx
      rw [Ideal.mem_radical_iff]
      refine ⟨unop n, ?_⟩
      exact (le_sup_left : I ^ unop n ≤ I ^ unop n ⊔ J ^ unop n)
        (Ideal.pow_mem_pow hx (unop n))
    · intro x hx
      rw [Ideal.mem_radical_iff]
      refine ⟨unop n, ?_⟩
      exact (le_sup_right : J ^ unop n ≤ I ^ unop n ⊔ J ^ unop n)
        (Ideal.pow_mem_pow hx (unop n))

/-- The simultaneous intersection-power diagram is initial in the full
category of ideals with radical containing `I ⊓ J`. -/
instance idealInfPowersToSelfLERadical_initial (I J : Ideal R) :
    Functor.Initial (idealInfPowersToSelfLERadical I J) where
  out K := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
        K.2 (isNoetherian_def.mp (inferInstance : IsNoetherian R R) _)
      obtain ⟨n, hn⟩ := exists_inf_pow_le_inf_pow I J m
      exact ⟨CostructuredArrow.mk
        (⟨⟨⟨hn.trans hm⟩⟩⟩ :
          (idealInfPowersToSelfLERadical I J).obj (op n) ⟶ K)⟩
    · intro x y
      apply Relation.ReflTransGen.single
      rcases le_total (unop x.left) (unop y.left) with h | h
      · right
        exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left
        exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

/-- The simultaneous supremum-power diagram is initial in the full category
of ideals with radical containing `I ⊔ J`. -/
instance idealSupPowersToSelfLERadical_initial (I J : Ideal R) :
    Functor.Initial (idealSupPowersToSelfLERadical I J) where
  out K := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
        K.2 (isNoetherian_def.mp (inferInstance : IsNoetherian R R) _)
      have hsup : I ^ n ⊔ J ^ n ≤ (I ⊔ J) ^ n :=
        sup_le
          (pow_le_pow_left' le_sup_left n)
          (pow_le_pow_left' le_sup_right n)
      exact ⟨CostructuredArrow.mk
        (⟨⟨⟨hsup.trans hn⟩⟩⟩ :
          (idealSupPowersToSelfLERadical I J).obj (op n) ⟶ K)⟩
    · intro x y
      apply Relation.ReflTransGen.single
      rcases le_total (unop x.left) (unop y.left) with h | h
      · right
        exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left
        exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

/-- The derived-Ext colimit over simultaneous intersection powers computes
local cohomology supported on `I ⊓ J`. -/
def derivedLocalCohomologyOfInfPowersIso
    (I J : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    derivedLocalCohomologyOfDiagram (idealInfPowersDiagram I J) M i ≅
      derivedLocalCohomology (I ⊓ J) M i :=
  HasColimit.isoOfNatIso (Iso.refl _) ≪≫
    derivedLocalCohomologyIsoOfInitial
      (idealInfPowersToSelfLERadical I J)
      (localCohomology.selfLERadicalDiagram (I ⊓ J)) M i ≪≫
    derivedLocalCohomologyIsoSelfLERadical (I ⊓ J) M i

/-- The derived-Ext colimit over simultaneous supremum powers computes
local cohomology supported on `I ⊔ J`. -/
def derivedLocalCohomologyOfSupPowersIso
    (I J : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    derivedLocalCohomologyOfDiagram (idealSupPowersDiagram I J) M i ≅
      derivedLocalCohomology (I ⊔ J) M i :=
  HasColimit.isoOfNatIso (Iso.refl _) ≪≫
    derivedLocalCohomologyIsoOfInitial
      (idealSupPowersToSelfLERadical I J)
      (localCohomology.selfLERadicalDiagram (I ⊔ J)) M i ≪≫
    derivedLocalCohomologyIsoSelfLERadical (I ⊔ J) M i

end Noetherian

end EtaleFundamentalGroups

end
