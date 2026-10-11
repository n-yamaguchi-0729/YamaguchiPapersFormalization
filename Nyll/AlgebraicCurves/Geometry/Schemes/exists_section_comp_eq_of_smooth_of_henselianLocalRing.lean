/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_section_comp_eq_of_smooth_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_etale_nhd_section_of_smooth
import Nyll.SchemeTheory.RingTheory.HenselianLocalRing_exists_algHom_lift_of_etale

/-!
# exists section comp eq of smooth of henselian Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_section_comp_eq_of_smooth_of_henselianLocalRing

universe u

namespace HensSection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem main
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ U)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ σ = x := by
  obtain ⟨E, _, _, _, 𝔫, _, h𝔫, hres, τ, hτf, hτx⟩ :=
    AlgebraicGeometry.exists_etale_nhd_section_of_smooth f x hx
  let q : ResidueField R →+* E ⧸ 𝔫 := Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫
  have hq : ∀ r : R, q (residue R r) = Ideal.Quotient.mk 𝔫 (algebraMap R E r) := fun r =>
    Ideal.quotientMap_mk
  have hqsurj : Function.Surjective q := fun t => by
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨r, hr⟩ := hres e
    refine ⟨residue R r, ?_⟩
    rw [hq, eq_comm, Ideal.Quotient.eq]
    exact hr
  have hqinj : Function.Injective q := q.injective
  let eqv : ResidueField R ≃+* E ⧸ 𝔫 := RingEquiv.ofBijective q ⟨hqinj, hqsurj⟩
  have heqv : ∀ a, eqv a = q a := fun _ => rfl
  let χ₀ : E →+* ResidueField R := eqv.symm.toRingHom.comp (Ideal.Quotient.mk 𝔫)
  have hχ₀ : ∀ r : R, χ₀ (algebraMap R E r) = residue R r := fun r => by
    change eqv.symm (Ideal.Quotient.mk 𝔫 (algebraMap R E r)) = residue R r
    rw [← hq, ← heqv, RingEquiv.symm_apply_apply]
  let χ : E →ₐ[R] ResidueField R := ⟨χ₀, hχ₀⟩
  obtain ⟨ψE, hψE⟩ := HenselianLocalRing.exists_algHom_lift_of_etale E χ
  refine ⟨Spec.map (CommRingCat.ofHom ψE.toRingHom) ≫ τ, ?_, ?_⟩
  · rw [Category.assoc, hτf, ← Spec.map_comp]
    have : CommRingCat.ofHom (algebraMap R E) ≫ CommRingCat.ofHom ψE.toRingHom = 𝟙 _ := by
      ext r
      exact ψE.commutes r
    rw [this, Spec.map_id]
  · have h1 : CommRingCat.ofHom ψE.toRingHom ≫ CommRingCat.ofHom (residue R) =
        CommRingCat.ofHom (Ideal.Quotient.mk 𝔫) ≫ CommRingCat.ofHom eqv.symm.toRingHom := by
      ext e
      exact hψE e
    rw [← Category.assoc, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc, hτx]
    change Spec.map (CommRingCat.ofHom eqv.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom q) ≫ x = x
    rw [← Category.assoc, ← Spec.map_comp]
    have h2' : eqv.symm.toRingHom.comp q = RingHom.id (ResidueField R) := RingHom.ext fun a =>
      eqv.symm_apply_apply a
    have h2 : CommRingCat.ofHom q ≫ CommRingCat.ofHom eqv.symm.toRingHom =
        𝟙 (CommRingCat.of (ResidueField R)) := by
      ext1
      exact h2'
    rw [h2]
    change Spec.map (𝟙 (CommRingCat.of (ResidueField R))) ≫ x = x
    rw [Spec.map_id, Category.id_comp]

end HensSection

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.exists_section_comp_eq_of_smooth_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ U)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ σ : Spec (CommRingCat.of R) ⟶ U, σ ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ σ = x :=
  HensSection.main f x hx
end AlgebraicCurves.Geometry.Schemes.Proofs.exists_section_comp_eq_of_smooth_of_henselianLocalRing
end ProofImplementation
