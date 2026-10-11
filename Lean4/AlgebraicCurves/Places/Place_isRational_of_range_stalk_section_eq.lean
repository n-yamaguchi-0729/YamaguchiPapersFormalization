/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Places.Evaluation

/-!
# Place is Rational of range stalk section eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_isRational_of_range_stalk_section_eq

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Opposite

namespace RatPlaceAux

theorem residue_germ_surjective (k : Type u) [Field k] :
    Function.Surjective (fun t : Γ(Spec (CommRingCat.of k), ⊤) =>
      (Spec (CommRingCat.of k)).residue (closedPoint k)
        ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial t)) := by
  intro z
  obtain ⟨s, rfl⟩ := (Spec (CommRingCat.of k)).residue_surjective (closedPoint k) z
  obtain ⟨U, hU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (Spec (CommRingCat.of k)).presheaf s
  have hUtop : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [Subsingleton.elim y (closedPoint k)]
    exact hU
  subst hUtop
  exact ⟨t, rfl⟩

end RatPlaceAux

open RatPlaceAux in
theorem _root_.AlgebraicCurve.Place.isRational_of_range_stalk_section_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ (v : AlgebraicCurve.Place k X.functionField),
      (algebraMap (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint k))) X.functionField).range =
        v.toValuationSubring.toSubring → v.IsRational := by
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  intro v hv
  set x : X := σ.base (closedPoint k) with hxdef
  let A : Type u := X.presheaf.stalk x
  let φ : A →+* X.functionField := algebraMap A X.functionField
  have hφinj : Function.Injective φ := IsFractionRing.injective A X.functionField
  let ι : k →+* Γ(Spec (CommRingCat.of k), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let toA : k →+* A := (X.presheaf.germ ⊤ x trivial).hom.comp (c.appTop.hom.comp ι)
  have hcompat : ∀ a : k, φ (toA a) = algebraMap k X.functionField a := by
    intro a
    change φ ((X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom (ι a))) =
      (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (c.appTop.hom (ι a))
    have := X.presheaf.germ_stalkSpecializes (U := ⊤) (y := x) trivial (x := genericPoint X)
      ((genericPoint_spec X).specializes (trivial : x ∈ (⊤ : Set X)))
    exact congrArg (fun f => f.hom (c.appTop.hom (ι a))) this
  let g : A →+* (Spec (CommRingCat.of k)).residueField (closedPoint k) :=
    ((Spec (CommRingCat.of k)).residue (closedPoint k)).hom.comp (σ.stalkMap (closedPoint k)).hom
  have hg : ∀ a : k, g (toA a) =
      (Spec (CommRingCat.of k)).residue (closedPoint k)
        ((Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial (ι a)) := by
    intro a
    change (Spec (CommRingCat.of k)).residue (closedPoint k)
        ((X.presheaf.germ ⊤ x trivial ≫ σ.stalkMap (closedPoint k)).hom (c.appTop.hom (ι a))) = _
    rw [Scheme.Hom.germ_stalkMap σ ⊤ (closedPoint k) trivial]
    change (Spec (CommRingCat.of k)).residue (closedPoint k)
        (((Spec (CommRingCat.of k)).presheaf.germ ⊤ (closedPoint k) trivial).hom ((c.appTop ≫
          σ.appTop).hom (ι a))) = _
    rw [← Scheme.Hom.comp_appTop, hσ, Scheme.Hom.id_appTop]
    rfl
  have hconst : ∀ s : A, ∃ a : k, s - toA a ∈ maximalIdeal A := by
    intro s
    obtain ⟨t, ht⟩ := residue_germ_surjective k (g s)
    obtain ⟨a, rfl⟩ := (Scheme.ΓSpecIso (CommRingCat.of
      k)).commRingCatIsoToRingEquiv.symm.surjective t
    refine ⟨a, ?_⟩
    have h0 : g (s - toA a) = 0 := by rw [map_sub, hg, sub_eq_zero]; exact ht.symm
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have : IsLocalRing ((Spec (CommRingCat.of k)).presheaf.stalk (closedPoint k)) :=
      (Spec (CommRingCat.of k)).toLocallyRingedSpace.isLocalRing (closedPoint k)
    exact IsUnit.ne_zero
      (M₀ := IsLocalRing.ResidueField
        ((Spec (CommRingCat.of k)).presheaf.stalk (closedPoint k))) (hu.map g) h0
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hy : (y : X.functionField) ∈ φ.range := by rw [hv]; exact y.2
  obtain ⟨s, hs⟩ := hy
  obtain ⟨a, ha⟩ := hconst s
  refine ⟨a, ?_⟩
  change Ideal.Quotient.mk _ (⟨algebraMap k X.functionField a, v.algebraMap_mem' a⟩ :
    v.toValuationSubring) = Ideal.Quotient.mk _ y
  rw [Ideal.Quotient.eq, mem_maximalIdeal, mem_nonunits_iff]
  have hm : toA a - s ∈ maximalIdeal A := by simpa using neg_mem ha
  rintro ⟨w, hw⟩
  have hw1 := congrArg Subtype.val w.val_inv
  rw [hw] at hw1
  obtain ⟨t, ht⟩ : ((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring).1 ∈ φ.range := by
    rw [hv]; exact ((w⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring).2
  have hval : ((⟨algebraMap k X.functionField a, v.algebraMap_mem' a⟩ : v.toValuationSubring) -
    y).1 = φ (toA a - s) := by
    change algebraMap k X.functionField a - (y : X.functionField) = _
    rw [map_sub, hcompat, hs]
  have hprod : φ ((toA a - s) * t) = φ 1 := by
    rw [map_mul, map_one, ← hval, ht]
    exact hw1
  have hunit : IsUnit (toA a - s) := IsUnit.of_mul_eq_one t (hφinj hprod)
  exact (mem_maximalIdeal _ |>.mp hm) hunit
end AlgebraicCurves.Places.Proofs.Place_isRational_of_range_stalk_section_eq
end ProofImplementation
