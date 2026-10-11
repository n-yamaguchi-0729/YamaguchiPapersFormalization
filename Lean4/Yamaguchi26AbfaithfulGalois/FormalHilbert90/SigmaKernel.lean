/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Theorem6Dot1FormalHilbert90
import ProCGroups.ProC.MaximalQuotients.ResidualAbelianizationPrimePowers
import ProCGroups.Abelian.PrimePowerCharacters

/-! # The kernel of the maximal abelian pro-Σ quotient inside an ambient group -/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups ProCGroups.ProC ProCGroups.Abelian

universe u

/-- The actual composite `A → A^Σ → (A^Σ)ᵃᵇ`. -/
def sigmaAbelianizationProjection (sigma : Set ℕ)
    (A : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A] :
    A →ₜ* TopologicalAbelianization (A ⧸ proCResidualCore (FiniteGroupClass.sigmaGroup sigma) A) :=
  (TopologicalAbelianization.mkₜ _).comp
    ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩

theorem sigmaAbelianizationProjection_apply (sigma : Set ℕ)
    (A : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A] (a : A) :
    sigmaAbelianizationProjection sigma A a =
      TopologicalAbelianization.mk _
        (QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) A) a) := rfl

/-- The manuscript's `R_Σ(D)`, viewed as a subgroup of the ambient group. -/
def sigmaResidualKernel {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) : Subgroup G :=
  (sigmaAbelianizationProjection sigma (D : Subgroup G)).toMonoidHom.ker.map
    (D : Subgroup G).subtype

theorem sigmaResidualKernel_le {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) : sigmaResidualKernel sigma D ≤ (D : Subgroup G) := by
  rintro _ ⟨d, _, rfl⟩
  exact d.property

theorem mem_sigmaResidualKernel_iff {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) (d : (D : Subgroup G)) :
    (d : G) ∈ sigmaResidualKernel sigma D ↔
      sigmaAbelianizationProjection sigma (D : Subgroup G) d = 1 := by
  constructor
  · rintro ⟨e, he, hed⟩
    have heq : e = d := Subtype.ext hed
    exact heq ▸ he
  · intro hd
    exact ⟨d, hd, rfl⟩

instance sigmaResidualKernel_normal {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) [(D : Subgroup G).Normal] :
    (sigmaResidualKernel sigma D).Normal := by
  have : CompactSpace (D : Subgroup G) := D.isClosed'.isClosedEmbedding_subtypeVal.compactSpace
  constructor
  rintro _ ⟨d, hd, rfl⟩ g
  refine ⟨MulAut.conjNormal g d, ?_, rfl⟩
  let e := TopologicalAbelianization.congr
    (residualQuotientConjugationContinuousMulEquiv
      (FiniteGroupClass.sigmaGroup_fullFormation sigma) (D : Subgroup G) D.isClosed' g)
  have he := congrArg e (show sigmaAbelianizationProjection sigma (D : Subgroup G) d = 1 from hd)
  change sigmaAbelianizationProjection sigma (D : Subgroup G) (MulAut.conjNormal g d) = 1
  rw [sigmaAbelianizationProjection_apply]
  dsimp only [e] at he
  rw [sigmaAbelianizationProjection_apply, TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk, map_one] at he
  exact he

theorem sigmaResidualKernel_isClosed {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) : IsClosed (sigmaResidualKernel sigma D : Set G) := by
  have : CompactSpace (D : Subgroup G) := D.isClosed'.isClosedEmbedding_subtypeVal.compactSpace
  exact ((ContinuousMonoidHom.isClosed_ker
    (sigmaAbelianizationProjection sigma (D : Subgroup G))).isCompact.image
    continuous_subtype_val).isClosed

/-- The intrinsic residual kernel is functorial for inclusions of closed subgroups. -/
theorem sigmaResidualKernel_mono {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (sigma : Set ℕ) (D E : ClosedSubgroup G) (hDE : (D : Subgroup G) ≤ (E : Subgroup G)) :
    sigmaResidualKernel sigma D ≤ sigmaResidualKernel sigma E := by
  have : CompactSpace (D : Subgroup G) := D.isClosed'.isClosedEmbedding_subtypeVal.compactSpace
  let i : (D : Subgroup G) →ₜ* (E : Subgroup G) :=
    ⟨Subgroup.inclusion hDE, continuous_subtype_val.subtype_mk _⟩
  let f := ProCGroups.QuotientGroup.mapₜ
    (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) (D : Subgroup G))
    (proCResidualCore (FiniteGroupClass.sigmaGroup sigma) (E : Subgroup G)) i
    (Subgroup.map_le_iff_le_comap.mp (map_proCResidualCore_le_of_continuousMonoidHom
      (FiniteGroupClass.sigmaGroup_fullFormation sigma).hereditary i))
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨i d, ?_, rfl⟩
  have heq := congrArg (TopologicalAbelianization.map f)
    (show sigmaAbelianizationProjection sigma (D : Subgroup G) d = 1 from hd)
  change sigmaAbelianizationProjection sigma (E : Subgroup G) (i d) = 1
  rw [sigmaAbelianizationProjection_apply]
  rw [sigmaAbelianizationProjection_apply, TopologicalAbelianization.map_apply_mk,
    map_one] at heq
  exact heq

/-- Elements killed by `D → (D^Σ)ᵃᵇ` have arbitrarily deep allowed prime-power roots
in the topological abelianization of `D`. -/
theorem sigmaResidualKernel_iff_primePower_roots {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) (d : (D : Subgroup G)) :
    (d : G) ∈ sigmaResidualKernel sigma D ↔
      ∀ p : ℕ, p ∈ sigma → p.Prime → ∀ n : ℕ, 0 < n →
        ∃ b : TopologicalAbelianization (D : Subgroup G),
          b ^ (p ^ n) = TopologicalAbelianization.mk (D : Subgroup G) d := by
  have : CompactSpace (D : Subgroup G) := D.isClosed'.isClosedEmbedding_subtypeVal.compactSpace
  rw [mem_sigmaResidualKernel_iff]
  have h := residualAbelianization_map_eq_iff_primePower (sigma := sigma) (D : Subgroup G)
    (TopologicalAbelianization.mk (D : Subgroup G) d) 1
  dsimp only at h
  rw [TopologicalAbelianization.map_apply_mk, map_one] at h
  change sigmaAbelianizationProjection sigma (D : Subgroup G) d = 1 ↔ _ at h
  simpa only [one_mul, eq_comm] using h

/-- The residual kernel is killed by each allowed primary projection. -/
theorem primaryProjection_eq_one_of_mem_sigmaResidualKernel {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) (d : (D : Subgroup G))
    (hd : (d : G) ∈ sigmaResidualKernel sigma D)
    (p : ℕ) [Fact p.Prime] (hp : p ∈ sigma) :
    QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p)
      (TopologicalAbelianization (D : Subgroup G)))
        (TopologicalAbelianization.mk (D : Subgroup G) d) = 1 := by
  have : CompactSpace (D : Subgroup G) := D.isClosed'.isClosedEmbedding_subtypeVal.compactSpace
  let A := TopologicalAbelianization (D : Subgroup G)
  have : TotallyDisconnectedSpace A := ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
    (Subgroup.closedCommutator (D : Subgroup G))
    (Subgroup.isClosed_closedCommutator (D : Subgroup G))
  let q := QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) A)
  have : IsClosed (proCResidualCore (FiniteGroupClass.pGroup p) A : Set A) :=
    proCResidualCore_isClosed (FiniteGroupClass.pGroup p) A
  have hQ := proCResidualCoreQuotient_hasOpenNormalBasisInClass
    (G := A) (FiniteGroupClass.pGroup_formation p)
  by_contra hne
  obtain ⟨n, hn, χ, hχ⟩ := exists_primePower_character_proP hQ hne
  obtain ⟨b, hb⟩ := (sigmaResidualKernel_iff_primePower_roots sigma D d).mp hd
    p hp (Fact.out : p.Prime) n hn
  apply hχ
  rw [← hb, map_pow, map_pow]
  apply Multiplicative.toAdd.injective
  change (p ^ n) • (χ (q b)).toAdd = 0
  simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- Vanishing of all allowed primary components detects the residual kernel. -/
theorem mem_sigmaResidualKernel_of_primaryProjections {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (sigma : Set ℕ) (D : ClosedSubgroup G) (d : (D : Subgroup G))
    (hd : ∀ (p : ℕ) [Fact p.Prime], p ∈ sigma →
      QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p)
        (TopologicalAbelianization (D : Subgroup G)))
          (TopologicalAbelianization.mk (D : Subgroup G) d) = 1) :
    (d : G) ∈ sigmaResidualKernel sigma D := by
  have : CompactSpace (D : Subgroup G) := D.isClosed'.isClosedEmbedding_subtypeVal.compactSpace
  let A := TopologicalAbelianization (D : Subgroup G)
  have : TotallyDisconnectedSpace A := ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
    (Subgroup.closedCommutator (D : Subgroup G))
    (Subgroup.isClosed_closedCommutator (D : Subgroup G))
  apply (sigmaResidualKernel_iff_primePower_roots sigma D d).mpr
  intro p hp hpprime n _
  have : Fact p.Prime := ⟨hpprime⟩
  let P : Subgroup A := (powMonoidHom (α := A) (p ^ n)).range
  let powerMap : A →ₜ* A := ⟨powMonoidHom (p ^ n), continuous_id.pow _⟩
  have hP : IsClosed (P : Set A) := ContinuousMonoidHom.isClosed_range powerMap
  have : IsClosed (P : Set A) := hP
  have : TotallyDisconnectedSpace (A ⧸ P) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal P hP
  have hQ : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) (A ⧸ P) := by
    apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
    intro U
    refine ⟨inferInstance, ?_⟩
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup (A ⧸ P)) q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective P b
    refine ⟨n, ?_⟩
    rw [← map_pow, ← map_pow]
    have hb : QuotientGroup.mk' P (b ^ (p ^ n)) = 1 :=
      (QuotientGroup.eq_one_iff (N := P) _).mpr ⟨b, rfl⟩
    rw [hb, map_one]
  have hle : proCResidualCore (FiniteGroupClass.pGroup p) A ≤ P :=
    proCResidualCore_le_of_proCQuotient P hP hQ
  exact hle ((QuotientGroup.eq_one_iff (N :=
    proCResidualCore (FiniteGroupClass.pGroup p) A) _).mp (hd p hp))

end Yamaguchi26AbfaithfulGalois
