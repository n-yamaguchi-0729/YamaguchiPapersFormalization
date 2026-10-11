/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Choose
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Scheme exists is Closed Immersion forall exists comp eq iff ideal eq bot
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace G0

variable (E : Scheme.{u})
  (I : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Ideal R)
  (hI : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶
    E),
      I R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (I R s).map ψ)

/-- The affine-open subtype supplies the hypothesis expected by affine chart maps. -/
private theorem affineOpenWitness {X : Scheme.{u}} (U : X.affineOpens) :
    IsAffineOpen U.1 := by
  change IsAffine U.1
  infer_instance

/-- The ideal assigned to the affine chart of `E` by the given functorial ideal rule. -/
def idealOf (U : E.affineOpens) : Ideal Γ(E, U) := I (Γ(E, U)) (affineOpenWitness U).fromSpec
include hI in
theorem idealOf_map {U V : E.affineOpens} (h : V.1 ≤ U.1) :
    (idealOf E I U).map (E.presheaf.map (homOfLE h).op).hom = idealOf E I V := by
  unfold idealOf
  rw [← hI, CommRingCat.ofHom_hom, IsAffineOpen.map_fromSpec (affineOpenWitness U)
    (affineOpenWitness V) (homOfLE h).op]

/-- The ideal sheaf data obtained by restricting the functorial ideal rule to affine opens. -/
def J : E.IdealSheafData where
  ideal U := idealOf E I U
  map_ideal_basicOpen U f := by
    have h := idealOf_map E I hI (U := U) (V := E.affineBasicOpen f) (E.basicOpen_le f)
    exact h

@[scoped simp] theorem J_ideal (U : E.affineOpens) : (J E I hI).ideal U = I (Γ(E, U))
  (affineOpenWitness U).fromSpec := rfl

section AffinePoints

variable (R : Type u) [CommRing R]

/-- The restriction from `R` to an affine open of its spectrum, via the canonical
global-sections isomorphism. -/
def ψV (V : (Spec (CommRingCat.of R)).affineOpens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom

theorem fromSpec_eq_specMap_ψV (V : (Spec (CommRingCat.of R)).affineOpens) :
    (affineOpenWitness V).fromSpec = Spec.map (CommRingCat.ofHom (ψV R V)) := by
  rw [ψV, CommRingCat.ofHom_hom, Spec.map_comp, ← IsAffineOpen.fromSpec_toSpecΓ, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

end AffinePoints

variable {E}

include hI in
theorem exists_theta {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E)
    (U : E.affineOpens) (V : (Spec (CommRingCat.of R)).affineOpens) (hV : V.1 ≤ s ⁻¹ᵁ U.1) :
    ∃ θ : Γ(E, U) ⟶ Γ(Spec (CommRingCat.of R), V),
      Spec.map θ ≫ (affineOpenWitness U).fromSpec = (affineOpenWitness V).fromSpec ≫ s ∧
      (idealOf E I U).map θ.hom = (I R s).map (ψV R V) := by
  have hrange : Set.range ((affineOpenWitness V).fromSpec ≫ s) ⊆ Set.range U.1.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : (affineOpenWitness V).fromSpec y ∈ (V.1 : Set _) := by
      have : (affineOpenWitness V).fromSpec y ∈ Set.range (affineOpenWitness V).fromSpec := ⟨y, rfl⟩
      rwa [IsAffineOpen.range_fromSpec] at this
    exact hV hy
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (IsOpenImmersion.lift U.1.ι _ hrange ≫ (affineOpenWitness
    U).isoSpec.hom)
  refine ⟨θ, ?_, ?_⟩
  · rw [hθ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι (hU := affineOpenWitness U),
      (affineOpenWitness U).isoSpec.hom_inv_id_assoc, IsOpenImmersion.lift_fac]
  · have h1 := hI (Γ(E, U)) (Γ(Spec (CommRingCat.of R), V)) θ.hom (affineOpenWitness U).fromSpec
    rw [CommRingCat.ofHom_hom] at h1
    have h2 := hI R (Γ(Spec (CommRingCat.of R), V)) (ψV R V) s
    rw [← fromSpec_eq_specMap_ψV] at h2
    unfold idealOf
    rw [← h1, ← h2]
    congr 1
    rw [hθ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι (hU := affineOpenWitness U),
      (affineOpenWitness U).isoSpec.hom_inv_id_assoc, IsOpenImmersion.lift_fac]

theorem iSup_small_eq_top {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E) :
    (⨆ V : {V : (Spec (CommRingCat.of R)).affineOpens // ∃ U : E.affineOpens, V.1 ≤ s ⁻¹ᵁ U.1},
      V.1.1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp E.isBasis_affineOpens)
    (TopologicalSpace.Opens.mem_top (s x))
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Spec (CommRingCat.of R)).isBasis_affineOpens)
      (show x ∈ s ⁻¹ᵁ U from hxU)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hVaff⟩, ⟨U, hU⟩, hVle⟩, hxV⟩
include hI in
theorem main : ∃ (Z : Scheme.{u}) (ι : Z ⟶ E), IsClosedImmersion ι ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        (∃ z : Spec (CommRingCat.of R) ⟶ Z, z ≫ ι = s) ↔ I R s = ⊥ := by
  refine ⟨(J E I hI).subscheme, (J E I hI).subschemeι, inferInstance, fun R _ s => ?_⟩
  let ι₀ := {V : (Spec (CommRingCat.of R)).affineOpens // ∃ U : E.affineOpens, V.1 ≤ s ⁻¹ᵁ U.1}
  have hU : ∀ V : ι₀, ∃ U : E.affineOpens, V.1.1 ≤ s ⁻¹ᵁ U.1 := fun V => V.2
  choose Uof hUof using hU
  let coverIdx (V : ι₀) : (J E I hI).subschemeCover.I₀ := by
    change E.affineOpens
    exact Uof V
  have hloc : ∀ V : ι₀, ∃ θ : Γ(E, Uof V) ⟶ Γ(Spec (CommRingCat.of R), V.1),
      Spec.map θ ≫ (affineOpenWitness (Uof V)).fromSpec = (affineOpenWitness V.1).fromSpec ≫ s ∧
      (idealOf E I (Uof V)).map θ.hom = (I R s).map (ψV R V.1) := fun V => exists_theta I hI s (Uof
        V) V.1 (hUof V)
  choose θ hθ₁ hθ₂ using hloc
  constructor
  · rintro ⟨z, hz⟩
    have hlocal : ∀ V : ι₀, (I R s).map (ψV R V.1) = ⊥ := by
      intro V
      rw [← hθ₂]
      have hr : Set.range ((affineOpenWitness V.1).fromSpec ≫ z) ⊆ Set.range ((J E I
        hI).subschemeCover.f (coverIdx V)) := by
        rintro _ ⟨y, rfl⟩
        have hrange : Set.range ((J E I hI).subschemeCover.f (coverIdx V)) =
            (J E I hI).subschemeι ⁻¹' (Uof V : Set E) :=
          congrArg (fun W : (J E I hI).subscheme.Opens => (W : Set (J E I hI).subscheme))
            ((J E I hI).opensRange_subschemeCover_map (Uof V))
        rw [hrange]
        change (J E I hI).subschemeι (z ((affineOpenWitness V.1).fromSpec y)) ∈ ((Uof V) : E.Opens)
        rw [← Scheme.Hom.comp_apply z, hz]
        have hy : (affineOpenWitness V.1).fromSpec y ∈ (V.1.1 : Set _) := by
          have : (affineOpenWitness V.1).fromSpec y ∈ Set.range (affineOpenWitness V.1).fromSpec :=
            ⟨y, rfl⟩
          rwa [IsAffineOpen.range_fromSpec] at this
        exact hUof V hy
      have hOI : IsOpenImmersion ((J E I hI).subschemeCover.f (coverIdx V)) :=
        (J E I hI).subschemeCover.map_prop (coverIdx V)
      obtain ⟨w, hw⟩ : ∃ w : Spec Γ(Spec (CommRingCat.of R), V.1) ⟶
          Spec (CommRingCat.of (Γ(E, Uof V) ⧸ idealOf E I (Uof V))),
          w ≫ (J E I hI).subschemeCover.f (coverIdx V) = (affineOpenWitness V.1).fromSpec ≫ z :=
        ⟨IsOpenImmersion.lift (H := hOI) ((J E I hI).subschemeCover.f (coverIdx V))
          ((affineOpenWitness V.1).fromSpec ≫ z) hr,
          IsOpenImmersion.lift_fac (H := hOI) ((J E I hI).subschemeCover.f (coverIdx V))
            ((affineOpenWitness V.1).fromSpec ≫ z) hr⟩
      obtain ⟨θ', hθ'⟩ := Spec.map_surjective w
      have e1 : (J E I hI).subschemeCover.f (coverIdx V) ≫ (J E I hI).subschemeι =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V)))) ≫
            (affineOpenWitness (Uof V)).fromSpec := by
        exact ((J E I hI).subschemeCover_map_subschemeι (Uof V)).trans
          ((J E I hI).glueDataObjι_ι (Uof V))
      have hcomp : w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V))))
        = Spec.map (θ V) := by
        apply (cancel_mono (affineOpenWitness (Uof V)).fromSpec).mp
        calc
          _ = w ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V)))) ≫
              (affineOpenWitness (Uof V)).fromSpec) := Category.assoc _ _ _
          _ = w ≫ ((J E I hI).subschemeCover.f (coverIdx V) ≫ (J E I hI).subschemeι) :=
            congrArg (w ≫ ·) e1.symm
          _ = (w ≫ (J E I hI).subschemeCover.f (coverIdx V)) ≫ (J E I hI).subschemeι :=
            (Category.assoc _ _ _).symm
          _ = ((affineOpenWitness V.1).fromSpec ≫ z) ≫ (J E I hI).subschemeι :=
            congrArg (· ≫ (J E I hI).subschemeι) hw
          _ = (affineOpenWitness V.1).fromSpec ≫ (z ≫ (J E I hI).subschemeι) :=
            Category.assoc _ _ _
          _ = (affineOpenWitness V.1).fromSpec ≫ s :=
            congrArg ((affineOpenWitness V.1).fromSpec ≫ ·) hz
          _ = Spec.map (θ V) ≫ (affineOpenWitness (Uof V)).fromSpec := (hθ₁ V).symm
      have hfac : CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V))) ≫ θ' = θ V :=
        Spec.map_injective ((Spec.map_comp _ θ').trans (by rw [hθ']; exact hcomp))
      have hring : (θ V).hom = θ'.hom.comp (Ideal.Quotient.mk (idealOf E I (Uof V))) :=
        (congrArg CommRingCat.Hom.hom hfac).symm
      rw [hring, ← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]
    rw [eq_bot_iff]
    intro x hx
    let σ : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv x
    have hσ : σ = 0 := by
      apply TopCat.Sheaf.eq_of_locally_eq' (Spec (CommRingCat.of R)).sheaf (fun V : ι₀ => V.1.1) ⊤
        (fun V => homOfLE le_top) (by rw [iSup_small_eq_top])
      intro V
      erw [map_zero]
      have hm : ψV R V.1 x ∈ (I R s).map (ψV R V.1) := Ideal.mem_map_of_mem _ hx
      rw [hlocal V, Ideal.mem_bot] at hm
      exact hm
    have : x = (Scheme.ΓSpecIso (.of R)).hom σ := by
      change x = ((Scheme.ΓSpecIso (.of R)).inv ≫ (Scheme.ΓSpecIso (.of R)).hom) x
      rw [Iso.inv_hom_id]; rfl
    rw [this, hσ, map_zero]
    exact Ideal.zero_mem _
  · intro hs
    have hker : ∀ (V : ι₀), ∀ a ∈ idealOf E I (Uof V), (θ V).hom a = 0 := by
      intro V a ha
      have h := hθ₂ V
      rw [hs, Ideal.map_bot, Ideal.map_eq_bot_iff_le_ker] at h
      exact h ha
    have e1 : ∀ V : ι₀, (J E I hI).subschemeCover.f (coverIdx V) ≫ (J E I hI).subschemeι =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V)))) ≫
          (affineOpenWitness (Uof V)).fromSpec := by
      intro V
      exact ((J E I hI).subschemeCover_map_subschemeι (Uof V)).trans
        ((J E I hI).glueDataObjι_ι (Uof V))
    let zloc : ∀ V : ι₀, (V.1.1 : Scheme.{u}) ⟶ (J E I hI).subscheme := fun V =>
      (affineOpenWitness V.1).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (R := Γ(E, Uof V) ⧸ idealOf E I (Uof V))
        (S := Γ(Spec (CommRingCat.of R), V.1))
        (Ideal.Quotient.lift (idealOf E I (Uof V)) (θ V).hom (hker V))) ≫
        (J E I hI).subschemeCover.f (coverIdx V)
    have hzloc : ∀ V : ι₀, zloc V ≫ (J E I hI).subschemeι = V.1.1.ι ≫ s := by
      intro V
      let φ : CommRingCat.of (Γ(E, Uof V) ⧸ idealOf E I (Uof V)) ⟶
          Γ(Spec (CommRingCat.of R), V.1) :=
        CommRingCat.ofHom (R := Γ(E, Uof V) ⧸ idealOf E I (Uof V))
          (S := Γ(Spec (CommRingCat.of R), V.1))
          (Ideal.Quotient.lift (idealOf E I (Uof V)) (θ V).hom (hker V))
      have hφ : CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V))) ≫ φ = θ V := by
        ext a
        rfl
      have hspec : Spec.map φ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal
        (Uof V)))) =
          Spec.map (θ V) :=
        (Spec.map_comp _ φ).symm.trans (congrArg Spec.map hφ)
      change ((affineOpenWitness V.1).isoSpec.hom ≫ Spec.map φ ≫
        (J E I hI).subschemeCover.f (coverIdx V)) ≫ (J E I hI).subschemeι = _
      calc
        _ = (affineOpenWitness V.1).isoSpec.hom ≫
            (Spec.map φ ≫ ((J E I hI).subschemeCover.f (coverIdx V) ≫ (J E I hI).subschemeι)) :=
          (Category.assoc _ _ _).trans
            (congrArg ((affineOpenWitness V.1).isoSpec.hom ≫ ·) (Category.assoc _ _ _))
        _ = (affineOpenWitness V.1).isoSpec.hom ≫
            (Spec.map φ ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof
              V)))) ≫
              (affineOpenWitness (Uof V)).fromSpec)) :=
          congrArg (fun k => (affineOpenWitness V.1).isoSpec.hom ≫ (Spec.map φ ≫ k)) (e1 V)
        _ = (affineOpenWitness V.1).isoSpec.hom ≫
            ((Spec.map φ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof
              V))))) ≫
              (affineOpenWitness (Uof V)).fromSpec) :=
          congrArg ((affineOpenWitness V.1).isoSpec.hom ≫ ·) (Category.assoc _ _ _).symm
        _ = (affineOpenWitness V.1).isoSpec.hom ≫
            (Spec.map (θ V) ≫ (affineOpenWitness (Uof V)).fromSpec) :=
          congrArg (fun k => (affineOpenWitness V.1).isoSpec.hom ≫
            (k ≫ (affineOpenWitness (Uof V)).fromSpec)) hspec
        _ = (affineOpenWitness V.1).isoSpec.hom ≫ ((affineOpenWitness V.1).fromSpec ≫ s) :=
          congrArg ((affineOpenWitness V.1).isoSpec.hom ≫ ·) (hθ₁ V)
        _ = ((affineOpenWitness V.1).isoSpec.hom ≫ (affineOpenWitness V.1).fromSpec) ≫ s :=
          (Category.assoc _ _ _).symm
        _ = V.1.1.ι ≫ s :=
          congrArg (· ≫ s) (affineOpenWitness V.1).isoSpec_hom_fromSpec
    let 𝒱 : (Spec (CommRingCat.of R)).OpenCover :=
      Scheme.Cover.mkOfCovers ι₀ (fun V => (V.1.1 : Scheme.{u})) (fun V => V.1.1.ι) (by
        intro x
        have hx : x ∈ (⨆ V : ι₀, V.1.1) := by rw [iSup_small_eq_top]; trivial
        obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨V, ⟨x, hV⟩, rfl⟩)
    refine ⟨𝒱.glueMorphisms zloc ?_, ?_⟩
    · change ∀ V W : ι₀,
        pullback.fst (𝒱.f V) (𝒱.f W) ≫ zloc V =
          pullback.snd (𝒱.f V) (𝒱.f W) ≫ zloc W
      intro V W
      rw [← cancel_mono (J E I hI).subschemeι]
      have h1 : (pullback.fst (𝒱.f V) (𝒱.f W) ≫ zloc V) ≫ (J E I hI).subschemeι =
          (pullback.fst (𝒱.f V) (𝒱.f W) ≫ 𝒱.f V) ≫ s := by
        exact (Category.assoc _ _ _).trans
          ((congrArg (pullback.fst (𝒱.f V) (𝒱.f W) ≫ ·) (hzloc V)).trans
            (Category.assoc _ _ _).symm)
      have h2 : (pullback.snd (𝒱.f V) (𝒱.f W) ≫ zloc W) ≫ (J E I hI).subschemeι =
          (pullback.snd (𝒱.f V) (𝒱.f W) ≫ 𝒱.f W) ≫ s := by
        exact (Category.assoc _ _ _).trans
          ((congrArg (pullback.snd (𝒱.f V) (𝒱.f W) ≫ ·) (hzloc W)).trans
            (Category.assoc _ _ _).symm)
      rw [h1, h2, pullback.condition]
    · apply Scheme.Cover.hom_ext 𝒱
      change ∀ V : ι₀, _
      intro V
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (J E I hI).subschemeι) (𝒱.ι_glueMorphisms zloc _ V)).trans (hzloc V))

end G0

attribute [local simp] G0.J_ideal


end

attribute [local simp] G0.J_ideal


theorem
  _root_.AlgebraicGeometry.Scheme.exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot
    (E : Scheme.{u})
    (I : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Ideal R)
    (hI : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R)
      ⟶ E),
      I R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (I R s).map ψ) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ E), IsClosedImmersion ι ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        (∃ z : Spec (CommRingCat.of R) ⟶ Z, z ≫ ι = s) ↔ I R s = ⊥ :=
  G0.main I hI
end Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
