/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkPuncturedSections
import Nyll.SchemeTheory.LocalGeometry.ClosedComplementPuncture
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Extending an open section across a closed complement point

When all missing points are closed, at each missing point
the open pulls back to the actual stalk puncture. Connectedness of its
actual strict-stalk puncture therefore extends a finite etale section to
the full stalk. The resulting section agrees on the native pullback of
the original open, as required for compatible neighborhood spreading.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicGeometry.FiniteEtale

/-- The local section required in 0BSA, constructed on the actual stalk
with its original overlap equation. -/
theorem exists_stalk_section_of_closed_complement
    {X Y : Scheme.{u}} (U : X.Opens)
    (hclosed : ∀ y : X, y ∉ U → IsClosed ({y} : Set X))
    (x : X) (hx : x ∉ U)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ : X.presheaf.stalk x →+* Ω) [IsLocalHom φ]
    [ConnectedSpace (Scheme.puncturedSpectrum
      (geometricStalk (Spec.map (CommRingCat.ofHom φ))))]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (s : U.toScheme ⟶ Y) (hs : s ≫ f = U.ι) :
    ∃ a : Spec (X.presheaf.stalk x) ⟶ Y,
      a ≫ f = X.fromSpecStalk x ∧
      pullback.snd (X.fromSpecStalk x) U.ι ≫ s =
        pullback.fst (X.fromSpecStalk x) U.ι ≫ a := by
  let S : Scheme.{u} := Spec (X.presheaf.stalk x)
  let q : S ⟶ X := X.fromSpecStalk x
  let j : Scheme.puncturedSpectrum (X.presheaf.stalk x) ⟶ S :=
    Scheme.puncturedSpectrumInclusion (X.presheaf.stalk x)
  let e : pullback q U.ι ≅ Scheme.puncturedSpectrum (X.presheaf.stalk x) :=
    Scheme.closedComplementPuncturedSpectrumPullbackIso U hclosed x hx
  have hej : e.hom ≫ j = pullback.fst q U.ι :=
    Scheme.closedComplementPuncturedSpectrumPullbackIso_hom_inclusion U hclosed x hx
  have heij : e.inv ≫ pullback.fst q U.ι = j := by
    rw [← hej, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  let s₀ : Scheme.puncturedSpectrum (X.presheaf.stalk x) ⟶ Y :=
    e.inv ≫ pullback.snd q U.ι ≫ s
  have hs₀ : s₀ ≫ f = j ≫ q := by
    change (e.inv ≫ pullback.snd q U.ι ≫ s) ≫ f = j ≫ q
    rw [Category.assoc, Category.assoc, hs, ← pullback.condition,
      ← Category.assoc, heij]
  let sP : Scheme.puncturedSpectrum (X.presheaf.stalk x) ⟶ pullback f q :=
    pullback.lift s₀ j hs₀
  have hsP : sP ≫ pullback.snd f q = j := pullback.lift_snd _ _ _
  obtain ⟨t, ht, _⟩ := existsUnique_section_of_connected_geometricStalk_puncture
    φ (pullback.snd f q) sP hsP
  let a : S ⟶ Y := t ≫ pullback.fst f q
  have haf : a ≫ f = q := by
    change (t ≫ pullback.fst f q) ≫ f = q
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht.1, Category.id_comp]
  have hja : j ≫ a = s₀ := by
    change j ≫ (t ≫ pullback.fst f q) = s₀
    rw [← Category.assoc, ht.2]
    exact pullback.lift_fst _ _ _
  refine ⟨a, haf, ?_⟩
  apply (cancel_epi e.inv).mp
  change e.inv ≫ (pullback.snd q U.ι ≫ s) = e.inv ≫ (pullback.fst q U.ι ≫ a)
  calc
    e.inv ≫ (pullback.snd q U.ι ≫ s) = s₀ := rfl
    _ = j ≫ a := hja.symm
    _ = e.inv ≫ (pullback.fst q U.ι ≫ a) :=
      (congrArg (fun z : Scheme.puncturedSpectrum (X.presheaf.stalk x) ⟶ S =>
        z ≫ a) heij).symm.trans (Category.assoc e.inv (pullback.fst q U.ι) a)

end AlgebraicGeometry.FiniteEtale
