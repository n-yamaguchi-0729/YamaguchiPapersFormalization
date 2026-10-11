/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom

/-!
# OModule Presheaf Aff Hom nonempty H0 equiv and HSucc equiv of bijective
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.AffHomCohomologyEquiv

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mCechIso

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
variable {F G : OModulePresheaf π} (φ : AffHom F G) (hφ : ∀ U : V.affineOpens, Function.Bijective
  (φ.app U))
variable (K : V.OrderedAffineCover)

include hφ in
theorem cochainMap_bijective (i : ℕ) : Function.Bijective (φ.cochainMap K i) := by
  constructor
  · intro x y h
    exact funext fun s => (hφ (K.affineInter π s)).1 (congrFun h s)
  · intro y
    exact ⟨fun s => ((hφ (K.affineInter π s)).2 (y s)).choose,
      funext fun s => ((hφ (K.affineInter π s)).2 (y s)).choose_spec⟩

/-- The cochain equivalence induced by the given sectionwise bijective morphism. -/
noncomputable def cochainEquiv (i : ℕ) : F.cochain K i ≃ₗ[R] G.cochain K i :=
  LinearEquiv.ofBijective (φ.cochainMap K i) (cochainMap_bijective φ hφ K i)

theorem cochainEquiv_apply (i : ℕ) (x : F.cochain K i) : cochainEquiv φ hφ K i x = φ.cochainMap K
  i x := rfl

theorem d_cochainEquiv (i : ℕ) (x : F.cochain K i) :
    G.d K i (cochainEquiv φ hφ K i x) = cochainEquiv φ hφ K (i + 1) (F.d K i x) := by
  rw [cochainEquiv_apply, cochainEquiv_apply, ← LinearMap.comp_apply, ← φ.cochainMap_comp_d K i]
  rfl

theorem map_ker (i : ℕ) :
    (LinearMap.ker (F.d K i)).map (cochainEquiv φ hφ K i : F.cochain K i →ₗ[R] G.cochain K i) =
      LinearMap.ker (G.d K i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LinearMap.mem_ker, LinearEquiv.coe_coe, d_cochainEquiv, LinearMap.mem_ker.mp hx, map_zero]
  · intro hy
    refine ⟨(cochainEquiv φ hφ K i).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    apply (cochainEquiv φ hφ K (i + 1)).injective
    rw [← d_cochainEquiv, LinearEquiv.apply_symm_apply, LinearMap.mem_ker.mp hy, map_zero]

/-- The induced equivalence of cocycle modules. -/
noncomputable def kerEquiv (i : ℕ) : LinearMap.ker (F.d K i) ≃ₗ[R] LinearMap.ker (G.d K i) :=
  LinearEquiv.ofSubmodules (cochainEquiv φ hφ K i) _ _ (map_ker φ hφ K i)

theorem kerEquiv_coe (i : ℕ) (x : LinearMap.ker (F.d K i)) :
    (kerEquiv φ hφ K i x : G.cochain K i) = φ.cochainMap K i x := rfl

theorem map_bdry (i : ℕ) :
    ((LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype).map
        (kerEquiv φ hφ K (i + 1) : LinearMap.ker (F.d K (i + 1)) →ₗ[R] LinearMap.ker (G.d K (i +
          1))) =
      (LinearMap.range (G.d K i)).comap (LinearMap.ker (G.d K (i + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]
  constructor
  · rintro ⟨x, ⟨c, hc⟩, rfl⟩
    refine ⟨cochainEquiv φ hφ K i c, ?_⟩
    rw [LinearEquiv.coe_coe, kerEquiv_coe, d_cochainEquiv, hc]
    rfl
  · rintro ⟨c, hc⟩
    refine ⟨(kerEquiv φ hφ K (i + 1)).symm y, ⟨(cochainEquiv φ hφ K i).symm c, ?_⟩,
      LinearEquiv.apply_symm_apply _ _⟩
    apply (cochainEquiv φ hφ K (i + 1)).injective
    rw [← d_cochainEquiv, LinearEquiv.apply_symm_apply, hc]
    have := congrArg (fun z : LinearMap.ker (G.d K (i + 1)) => (z : G.cochain K (i + 1)))
      (LinearEquiv.apply_symm_apply (kerEquiv φ hφ K (i + 1)) y)
    exact this.symm

/-- The induced linear equivalence on positive-degree Čech cohomology. -/
noncomputable def HSuccEquiv (i : ℕ) : F.HSucc K i ≃ₗ[R] G.HSucc K i :=
  Submodule.Quotient.equiv _ _ (kerEquiv φ hφ K (i + 1)) (map_bdry φ hφ K i)

include φ hφ in
theorem main :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i) :=
  ⟨⟨kerEquiv φ hφ K 0⟩, fun i => ⟨HSuccEquiv φ hφ K i⟩⟩

end P2mCechIso

theorem
  _root_.AlgebraicGeometry.OModulePresheaf.AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F G : OModulePresheaf π} (φ : OModulePresheaf.AffHom F G)
    (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U)) (K : V.OrderedAffineCover) :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K) ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K i) :=
  P2mCechIso.main φ hφ K
end AlgebraicCurves.Cohomology.Sheaves.Proofs.AffHomCohomologyEquiv
end ProofImplementation
