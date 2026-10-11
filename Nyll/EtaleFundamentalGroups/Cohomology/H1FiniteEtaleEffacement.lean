/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterPullback
import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalFundamentalGroup
import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Nat.Prime.Basic

/-!
# Killing actual finite-coefficient H¹ on a finite étale cover

The open kernel of the actual cohomology character is realized by an actual
connected finite étale cover. Geometric naturality proves that the original
derived cohomology class pulls back to zero.

This supplies the degree-one step of Mochizuki, "The Local Pro-p Anabelian
Geometry of Curves", Lemma 0.4, pp. 14–15:
https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Local%20Pro-p%20Anabelian%20Geometry%20of%20Curves.pdf

The result here allows any finite abelian constant coefficients and asserts
finite étale effacement, with geometric fiber degree dividing the order of
the coefficient group. The higher-degree K(pi,1) comparison is not asserted.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Cohomology

/-- Every actual finite constant-coefficient H¹ class becomes zero on an
actual connected finite étale Galois cover, with degree dividing the order of
the coefficient group and a lift of the original base point. -/
theorem exists_galois_finiteEtale_cover_killing_h1
    {X : Scheme.{u}} [ConnectedSpace X]
    (C : AddCommGrpCat.{u}) [Finite C]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1) :
    ∃ (V : FiniteEtale X) (_ : IsGalois V)
      (xiV : Spec (.of Ω) ⟶ V.left),
      xiV ≫ V.hom = xi ∧
        Nat.card ((FiniteEtale.fiber xi).obj V) ∣ Nat.card C ∧
        (Nat.card ((FiniteEtale.fiber xi).obj V) = 1 ↔ a = 0) ∧
        constantCohomologyPullback (X := V.left) (Y := X) V.hom C 1 a = 0 := by
  let : TopologicalSpace (Multiplicative C) := ⊥
  have : DiscreteTopology (Multiplicative C) := ⟨rfl⟩
  let χ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative C := h1Character C xi a
  let U : OpenNormalSubgroup (Aut (FiniteEtale.fiber xi)) :=
    { toSubgroup := χ.toMonoidHom.ker
      isOpen' := χ.continuous.isOpen_preimage _ (isOpen_discrete _) }
  obtain ⟨V, hV, xiV, hxi, e, hcard, he⟩ :=
    FiniteEtale.exists_galoisCover_lift_fundamentalGroup_equiv_openNormal_compatible xi U
  have : IsGalois V := hV
  have : ConnectedSpace V.left := FiniteEtale.connectedSpace_left_of_isConnected V
  have hdegree : Nat.card ((FiniteEtale.fiber xi).obj V) ∣ Nat.card C := by
    rw [hcard]
    change χ.toMonoidHom.ker.index ∣ Nat.card C
    rw [Subgroup.index_ker]
    exact χ.toMonoidHom.range.card_subgroup_dvd_card
  have hone : Nat.card ((FiniteEtale.fiber xi).obj V) = 1 ↔ a = 0 := by
    rw [hcard]
    change χ.toMonoidHom.ker.index = 1 ↔ a = 0
    rw [Subgroup.index_eq_one, MonoidHom.ker_eq_top_iff]
    constructor
    · intro h
      apply (h1Character_eq_one_iff C xi a).mp
      apply ContinuousMonoidHom.ext
      intro g
      exact DFunLike.congr_fun h g
    · intro ha
      exact congrArg ContinuousMonoidHom.toMonoidHom
        ((h1Character_eq_one_iff C xi a).mpr ha)
  refine ⟨V, hV, xiV, hxi, hdegree, hone, ?_⟩
  apply (h1Character_eq_one_iff C xiV _).mp
  rw [← h1Character_schemePullback (X := V.left) (Y := X) V.hom C xiV a]
  apply ContinuousMonoidHom.ext
  intro g
  have hmem : (hxi ▸ FiniteEtale.fundamentalGroupHom V.hom xiV g) ∈ U := by
    rw [← he g]
    exact (e g).property
  have hker : χ (hxi ▸ FiniteEtale.fundamentalGroupHom V.hom xiV g) = 1 := hmem
  subst xi
  exact hker


/-- The connected-cover form of finite constant-coefficient H¹ effacement. -/
theorem exists_connected_finiteEtale_cover_killing_h1
    {X : Scheme.{u}} [ConnectedSpace X]
    (C : AddCommGrpCat.{u}) [Finite C]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1) :
    ∃ (V : FiniteEtale X) (_ : ConnectedSpace V.left)
      (xiV : Spec (.of Ω) ⟶ V.left),
      xiV ≫ V.hom = xi ∧
        constantCohomologyPullback (X := V.left) (Y := X) V.hom C 1 a = 0 := by
  obtain ⟨V, hV, xiV, hxi, _, _, ha⟩ := exists_galois_finiteEtale_cover_killing_h1 C xi a
  have : IsGalois V := hV
  exact ⟨V, FiniteEtale.connectedSpace_left_of_isConnected V, xiV, hxi, ha⟩


/-- For a finite p-primary coefficient group, the killing cover has p-power
geometric degree, bounded by the order of the coefficient group. -/
theorem exists_primePower_galois_finiteEtale_cover_killing_h1
    {X : Scheme.{u}} [ConnectedSpace X]
    (C : AddCommGrpCat.{u}) [Finite C]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X)
    (p n : ℕ) (hp : p.Prime) (hC : Nat.card C = p ^ n)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1) :
    ∃ (V : FiniteEtale X) (_ : IsGalois V)
      (xiV : Spec (.of Ω) ⟶ V.left) (m : ℕ),
      xiV ≫ V.hom = xi ∧ m ≤ n ∧
        Nat.card ((FiniteEtale.fiber xi).obj V) = p ^ m ∧
        constantCohomologyPullback (X := V.left) (Y := X) V.hom C 1 a = 0 := by
  obtain ⟨V, hV, xiV, hxi, hdegree, _, ha⟩ :=
    exists_galois_finiteEtale_cover_killing_h1 C xi a
  rw [hC] at hdegree
  obtain ⟨m, hm, heq⟩ := (Nat.dvd_prime_pow hp).mp hdegree
  exact ⟨V, hV, xiV, m, hxi, hm, heq, ha⟩


/-- A nonzero H¹ class with coefficients of prime order is killed by a
connected Galois cover of exactly that prime degree. -/
theorem exists_primeDegree_galois_finiteEtale_cover_killing_h1
    {X : Scheme.{u}} [ConnectedSpace X]
    (C : AddCommGrpCat.{u}) [Finite C]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X)
    (p : ℕ) (hp : p.Prime) (hC : Nat.card C = p)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj C) 1)
    (ha : a ≠ 0) :
    ∃ (V : FiniteEtale X) (_ : IsGalois V)
      (xiV : Spec (.of Ω) ⟶ V.left),
      xiV ≫ V.hom = xi ∧
        Nat.card ((FiniteEtale.fiber xi).obj V) = p ∧
        constantCohomologyPullback (X := V.left) (Y := X) V.hom C 1 a = 0 := by
  obtain ⟨V, hV, xiV, hxi, hdegree, hone, hzero⟩ :=
    exists_galois_finiteEtale_cover_killing_h1 C xi a
  rw [hC] at hdegree
  have hne : Nat.card ((FiniteEtale.fiber xi).obj V) ≠ 1 :=
    fun h => ha (hone.mp h)
  exact ⟨V, hV, xiV, hxi, ((Nat.dvd_prime hp).mp hdegree).resolve_left hne, hzero⟩

end EtaleFundamentalGroups.Cohomology
