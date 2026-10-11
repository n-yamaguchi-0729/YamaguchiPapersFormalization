/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions

/-!
# OModule Presheaf is Coherent is Quasicoherent supported In pushforward Unit
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace P2mPushUnit

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)
  [IsClosedImmersion ι]

omit [IsClosedImmersion ι] in
theorem preimage_eq_bot (U : V.Opens) (hU : (U : Set V) ∩ Set.range ι.base = ∅) : ι ⁻¹ᵁ U = ⊥ := by
  ext z
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot,
    Set.mem_empty_iff_false, iff_false]
  intro hz
  have : ι.base z ∈ (U : Set V) ∩ Set.range ι.base := ⟨hz, ⟨z, rfl⟩⟩
  rw [hU] at this
  exact this

theorem subsingleton_sections_of_eq_bot (W : Z.Opens) (h : W = ⊥) : Subsingleton Γ(Z, W) := by
  subst h
  infer_instance

/-- The closed image of the given closed immersion. -/
def image : Closeds V := ⟨Set.range ι.base, ι.isClosedEmbedding.isClosed_range⟩

theorem coe_image : (image ι : Set V) = Set.range ι.base := rfl

theorem supportedIn : (pushforwardUnit π ι).SupportedIn (image ι) := fun U hU =>
  subsingleton_sections_of_eq_bot (ι ⁻¹ᵁ U.1) (preimage_eq_bot ι U.1 hU)

theorem res_rfl (W : Z.Opens) (x : Γ(Z, W)) : Z.presheaf.map (homOfLE (le_refl W)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), Z.presheaf.map_id]; rfl

omit [IsClosedImmersion ι] in
theorem appLE_rfl_apply (U : V.Opens) (a : Γ(V, U)) : ι.appLE U (ι ⁻¹ᵁ U) le_rfl a = ι.app U a := by
  change Z.presheaf.map (homOfLE (le_refl _)).op (ι.app U a) = _
  exact res_rfl (ι ⁻¹ᵁ U) _

/-- The section map of the closed immersion viewed as a linear map to the pushforward of its
structure sheaf. -/
noncomputable def actHom (U : V.affineOpens) : Γ(V, U.1) →ₗ[Γ(V, U.1)] (pushforwardUnit π ι).obj
  U.1 where
  toFun a := show Γ(Z, ι ⁻¹ᵁ U.1) from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a
  map_add' a b := map_add _ a b
  map_smul' a b := by
    change ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (a * b) = ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * ι.appLE U.1
      (ι ⁻¹ᵁ U.1) le_rfl b
    exact map_mul _ a b

theorem actHom_surjective (U : V.affineOpens) : Function.Surjective (actHom π ι U) := by
  intro x
  obtain ⟨a, ha⟩ := ι.app_surjective U.1 U.2 x
  exact ⟨a, (appLE_rfl_apply ι U.1 a).trans ha⟩

theorem isCoherent : (pushforwardUnit π ι).IsCoherent := fun U =>
  Module.Finite.of_surjective (actHom π ι U) (actHom_surjective π ι U)

theorem loc_core (U : V.affineOpens) (g : Γ(Z, ι ⁻¹ᵁ U.1)) (W' : Z.Opens) (hle : W' ≤ ι ⁻¹ᵁ U.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(Z, W'), ∃ (n : ℕ) (y : Γ(Z, ι ⁻¹ᵁ U.1)),
        Z.presheaf.map (homOfLE hle).op y = Z.presheaf.map (homOfLE hle).op (g ^ n) * x) ∧
      (∀ y : Γ(Z, ι ⁻¹ᵁ U.1), Z.presheaf.map (homOfLE hle).op y = 0 → ∃ n : ℕ, g ^ n * y = 0) := by
  subst hW'
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have : IsLocalization.Away g Γ(Z, Z.basicOpen g) := hW.isLocalization_basicOpen g
  have halg : ∀ y : Γ(Z, ι ⁻¹ᵁ U.1),
      algebraMap Γ(Z, ι ⁻¹ᵁ U.1) Γ(Z, Z.basicOpen g) y = Z.presheaf.map (homOfLE hle).op y := fun y
        => by
    rw [Subsingleton.elim (homOfLE hle) (homOfLE (Z.basicOpen_le g))]; rfl
  constructor
  · intro x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨n, y, ?_⟩
    rw [← halg, ← halg, ← h, mul_comm]
  · intro y hy
    rw [← halg] at hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hy
    exact ⟨n, hn⟩

omit [IsClosedImmersion ι] in
theorem preimage_basicOpen_eq (U : V.affineOpens) (f : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen f = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f) := by
  rw [appLE_rfl_apply]; exact Scheme.preimage_basicOpen ι f

omit [IsClosedImmersion ι] in
theorem pre_le (U : V.affineOpens) (f : Γ(V, U.1)) : ι ⁻¹ᵁ V.basicOpen f ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le f hx

omit [IsClosedImmersion ι] in
theorem smul_basicOpen (U : V.affineOpens) (f : Γ(V, U.1)) (a : Γ(V, U.1)) (x : Γ(Z, ι ⁻¹ᵁ
  V.basicOpen f)) :
    ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom a •
        (show (pushforwardUnit π ι).obj (V.basicOpen f) from x)) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from
        Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) * x) := by
  change ι.appLE (V.basicOpen f) (ι ⁻¹ᵁ V.basicOpen f) le_rfl ((V.presheaf.map (homOfLE
    (V.basicOpen_le f)).op) a) * x
    = _
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

omit [IsClosedImmersion ι] in
theorem smul_top (U : V.affineOpens) (a : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (a • (show (pushforwardUnit π ι).obj U.1 from y)) =
      (show (pushforwardUnit π ι).obj U.1 from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * y) := rfl

omit [IsClosedImmersion ι] in
theorem res_eq (U : V.affineOpens) (f : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (pushforwardUnit π ι).res (V.basicOpen_le f) (show (pushforwardUnit π ι).obj U.1 from y) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from Z.presheaf.map (homOfLE (pre_le ι U
        f)).op y) := by
  change Z.presheaf.map _ y = _
  rw [Subsingleton.elim (homOfLE ((Opens.map ι.base).monotone (V.basicOpen_le f))) (homOfLE (pre_le
    ι U f))]

theorem isQuasicoherent : (pushforwardUnit π ι).IsQuasicoherent := by
  intro U f
  set g : Γ(Z, ι ⁻¹ᵁ U.1) := ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f with hg
  obtain ⟨h1, h2⟩ := loc_core ι U g (ι ⁻¹ᵁ V.basicOpen f) (pre_le ι U f) (preimage_basicOpen_eq ι U
    f)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨n, y, ?_⟩
    erw [res_eq, smul_basicOpen]
    change Z.presheaf.map (homOfLE (pre_le ι U f)).op y =
      Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n)) *
        (show Γ(Z, ι ⁻¹ᵁ V.basicOpen f) from x)
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hy
  · intro y hy
    erw [res_eq] at hy
    obtain ⟨n, hn⟩ := h2 y hy
    refine ⟨n, ?_⟩
    erw [smul_top]
    change ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n) * (show Γ(Z, ι ⁻¹ᵁ U.1) from y) = 0
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hn

theorem main :
    (pushforwardUnit π ι).IsCoherent ∧ (pushforwardUnit π ι).IsQuasicoherent ∧
      (pushforwardUnit π ι).SupportedIn ⟨Set.range ι.base, ι.isClosedEmbedding.isClosed_range⟩ :=
  ⟨isCoherent π ι, isQuasicoherent π ι, supportedIn π ι⟩

end P2mPushUnit

theorem
  _root_.AlgebraicGeometry.OModulePresheaf.isCoherent_isQuasicoherent_supportedIn_pushforwardUnit
    {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)
      [IsClosedImmersion ι] :
    (OModulePresheaf.pushforwardUnit π ι).IsCoherent ∧ (OModulePresheaf.pushforwardUnit π
      ι).IsQuasicoherent ∧
      (OModulePresheaf.pushforwardUnit π ι).SupportedIn ⟨Set.range ι.base,
        ι.isClosedEmbedding.isClosed_range⟩ :=
  P2mPushUnit.main π ι
end OModulePresheaf_isCoherent_isQuasicoherent_supportedIn_pushforwardUnit
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
