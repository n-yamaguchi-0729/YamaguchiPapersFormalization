/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Models.Finite_compl_of_isOpen
import AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint

/-!
# Finite fibres of a polynomial map from an open of a curve

A transcendental section on a nonempty open of an integral smooth curve defines
a map to the polynomial spectrum whose point fibres are finite.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Opens_finite_preimage_singleton_toSpecPolynomial

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Polynomial
open _root_.TopologicalSpace
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))

namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Opens
open _root_.AlgebraicGeometry.Scheme.Opens
end Scheme.Opens
open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Opens in
/-- The base field homomorphism into global sections on the open subscheme. -/
noncomputable abbrev Scheme.Opens.baseRingHom (U : C.Opens) : k →+* Γ((U : Scheme.{u}), ⊤) :=
  (U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Opens in
/-- The morphism to the affine line defined by a section on the open subscheme. -/
noncomputable abbrev Scheme.Opens.toSpecPolynomial (U : C.Opens) (s : Γ(C, U)) :
    (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k[X]) :=
  (U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s)))

open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Opens in
theorem Scheme.Opens.toSpecPolynomial_comp_C (U : C.Opens) (s : Γ(C, U)) :
    Scheme.Opens.toSpecPolynomial c U s ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) =
      U.ι ≫ c := by
  simp only [Scheme.Opens.toSpecPolynomial, Category.assoc]
  have h1 : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫ CommRingCat.ofHom
      (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.ι ≫ c).appTop := by
    ext a
    simp [Scheme.Opens.baseRingHom]
  have hc : Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫ CommRingCat.ofHom
        (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s))) =
      Spec.map (CommRingCat.ofHom
        (Polynomial.eval₂RingHom (Scheme.Opens.baseRingHom c U) (U.topIso.inv s))) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) := Spec.map_comp _ _
  refine ((congrArg (fun m : Spec Γ(↑U, ⊤) ⟶ Spec (CommRingCat.of k) =>
    (U : Scheme.{u}).toSpecΓ ≫ m) hc).symm.trans
      (congrArg (fun m : CommRingCat.of k ⟶ Γ(↑U, ⊤) =>
        (U : Scheme.{u}).toSpecΓ ≫ Spec.map m) h1)).trans ?_
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

namespace QFin

theorem germToFunctionField_map [IsIntegral C] {U V : C.Opens} [Nonempty U] [Nonempty V]
    (i : V ⟶ U) (t : Γ(C, U)) :
    (C.germToFunctionField V).hom ((C.presheaf.map i.op).hom t) = (C.germToFunctionField U).hom
        t := by
  change (C.presheaf.map i.op ≫ C.germToFunctionField V).hom t = _
  rw [Scheme.germToFunctionField, C.presheaf.germ_res]

theorem mem_toSpecΓ_asIdeal_iff (X : Scheme.{u}) (x : X) (t : Γ(X, ⊤)) :
    t ∈ (X.toSpecΓ.base x).asIdeal ↔ x ∉ X.basicOpen t := by
  have h : x ∈ X.basicOpen t ↔ t ∉ (X.toSpecΓ.base x).asIdeal := by
    rw [← X.toSpecΓ_preimage_basicOpen t]; rfl
  rw [h, not_not]

theorem mem_fibre_iff (U : C.Opens) (s : Γ(C, U)) (x : (U : Scheme.{u})) (q : k[X]) :
    q ∈ ((Scheme.Opens.toSpecPolynomial c U s).base x).asIdeal ↔
      x.1 ∉ C.basicOpen
        (Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q) := by
  let t : Γ(↑U, ⊤) := Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q
  have hb : x ∈ (U : Scheme.{u}).basicOpen t ↔ x.1 ∈ C.basicOpen t :=
    Scheme.Opens.mem_basicOpen_toScheme (x := (show U from x))
  exact (mem_toSpecΓ_asIdeal_iff (U : Scheme.{u}) x t).trans (not_congr hb)

variable [IsIntegral C]

theorem germToFunctionField_eval₂ (U : C.Opens) [Nonempty U] (s : Γ(C, U)) (q : k[X]) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    haveI : Nonempty (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]; infer_instance
    (C.germToFunctionField (U.ι ''ᵁ ⊤)).hom
        (Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q) =
      Polynomial.aeval (C.germToFunctionField U s) q := by
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have : Nonempty (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]; infer_instance
  dsimp only
  rw [Polynomial.aeval_def]
  have he := Polynomial.hom_eval₂ (p := q) (f := Scheme.Opens.baseRingHom c U)
    (g := (C.germToFunctionField (U.ι ''ᵁ ⊤)).hom) (x := U.topIso.inv s)
  refine he.trans ?_
  congr 1
  · ext a
    change (C.germToFunctionField (U.ι ''ᵁ ⊤)).hom ((U.ι ≫ c).appTop.hom _) =
      AlgebraicCurve.baseToFunctionField c a
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Opens.ι_appTop]
    have hc : C.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op ≫
        C.germToFunctionField (U.ι ''ᵁ ⊤) = C.presheaf.germ ⊤ (genericPoint C) trivial := by
      rw [Scheme.germToFunctionField, C.presheaf.germ_res]
    exact congrArg (fun φ => φ.hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        a))) hc
  · rw [Scheme.Opens.topIso_inv]
    exact germToFunctionField_map _ s

end QFin

end AlgebraicGeometry

with_weak_namespace _root_.AlgebraicCurves.Geometry.Schemes.Proofs
open _root_.AlgebraicGeometry
    Scheme_Opens_finite_preimage_singleton_toSpecPolynomial.AlgebraicGeometry
    Scheme_Opens_finite_preimage_singleton_toSpecPolynomial.AlgebraicGeometry.QFin in
with_weak_namespace Scheme_Opens_finite_preimage_singleton_toSpecPolynomial
theorem _root_.AlgebraicGeometry.Scheme.Opens.finite_preimage_singleton_toSpecPolynomial
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s))
    (p : Spec (CommRingCat.of k[X])) :
    (((U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of
          k)).inv.hom)
        (U.topIso.inv s)))).base ⁻¹' {p}).Finite := by
  change ((Scheme.Opens.toSpecPolynomial c U s).base ⁻¹' {p}).Finite
  classical
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have hne' : Nonempty (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]; infer_instance
  have hsec : ∀ q : k[X], q ≠ 0 →
      Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q ≠ 0 := by
    intro q hq h0
    apply hs
    refine ⟨q, hq, ?_⟩
    rw [← germToFunctionField_eval₂ c U s q]
    exact (map_eq_zero_iff (C.germToFunctionField (U.ι ''ᵁ ⊤)).hom
      (C.germToFunctionField_injective _)).mpr h0
  by_cases hp : p.asIdeal = ⊥
  · have : Smooth c := SmoothOfRelativeDimension.smooth (n := 1) (f := c)
    have : LocallyOfFiniteType (Scheme.Opens.toSpecPolynomial c U s ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
      rw [Scheme.Opens.toSpecPolynomial_comp_C]; infer_instance
    have : LocallyOfFiniteType (Scheme.Opens.toSpecPolynomial c U s) :=
      locallyOfFiniteType_of_comp _ (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
    apply Set.Subsingleton.finite
    intro x hx y hy
    have hx' : (Scheme.Opens.toSpecPolynomial c U s).base x = p := hx
    have hy' : (Scheme.Opens.toSpecPolynomial c U s).base y = p := hy
    have hgen : ∀ z : (U : Scheme.{u}), (Scheme.Opens.toSpecPolynomial c U s).base z = p →
        z.1 = genericPoint C := by
      intro z hz
      by_contra hzη
      have hzC : IsClosed ({z.1} : Set C) :=
        AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c z.1 hzη
      have hzU : IsClosed ({z} : Set (U : Scheme.{u})) := by
        have : ({z} : Set (U : Scheme.{u})) = Subtype.val ⁻¹' {z.1} := by
          ext w
          simp only [Set.mem_singleton_iff]
          exact Subtype.ext_iff
        rw [this]
        exact hzC.preimage continuous_subtype_val
      have hcl := (Scheme.Opens.toSpecPolynomial c U s).closePoints_subset_preimage_closedPoints hzU
      have hcl' : IsClosed ({p} : Set (PrimeSpectrum k[X])) := by rw [← hz]; exact hcl
      have hmax : p.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hcl'
      rw [hp] at hmax
      exact Polynomial.not_isField k (Ring.isField_iff_maximal_bot.mpr hmax)
    exact Subtype.ext ((hgen x hx').trans (hgen y hy').symm)
  · obtain ⟨q, hqp, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    set r := Polynomial.eval₂ (Scheme.Opens.baseRingHom c U) (U.topIso.inv s) q with hrdef
    have hr0 : r ≠ 0 := hsec q hq0
    have hopen : ((C.basicOpen r : C.Opens) : Set C).Nonempty := by
      rw [Set.nonempty_iff_ne_empty, Ne, ← Opens.coe_bot, SetLike.coe_set_eq]
      intro hbot
      exact hr0 ((basicOpen_eq_bot_iff (X := C) (U := U.ι ''ᵁ ⊤) r).mp hbot)
    have hfin := AlgebraicCurve.finite_compl_of_isOpen c (C.basicOpen r) hopen
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro x hx
    have hx' : (Scheme.Opens.toSpecPolynomial c U s).base x = p := hx
    change x.1 ∈ ((C.basicOpen r : C.Opens) : Set C)ᶜ
    rw [Set.mem_compl_iff, SetLike.mem_coe]
    exact (mem_fibre_iff c U s x q).mp (hx' ▸ hqp)
end Scheme_Opens_finite_preimage_singleton_toSpecPolynomial
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
