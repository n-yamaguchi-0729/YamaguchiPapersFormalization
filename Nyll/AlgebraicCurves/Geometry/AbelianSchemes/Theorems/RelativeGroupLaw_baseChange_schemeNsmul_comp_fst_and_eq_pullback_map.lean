/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange

/-!
# Relative Group Law base Change scheme Nsmul comp fst and eq pullback map
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


universe u

namespace GoodReductionJacobian

export _root_.GoodReductionJacobian (schemeHomOverComp RelativeGroupLaw)

namespace RelativeGroupLaw

export _root_.GoodReductionJacobian.RelativeGroupLaw (baseChangeStr baseChangePointToBase
  baseChangePointOfBase baseChangePointToBase_coe baseChangePointOfBase_coe
  baseChangePointToBase_ofBase baseChange baseChange_mul nsmul nsmul_succ nsmul_natural idPoint
  schemeNsmul schemeNsmul_over basePointInclusion)


open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian


variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem baseChange_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of
  R')) (n : ℕ)
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).nsmul t' n x = baseChangePointOfBase ι (G.nsmul _ n (baseChangePointToBase ι
      x)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, ih, baseChange_mul, baseChangePointToBase_ofBase, nsmul_succ]

theorem nsmul_coe_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hid : schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := Subtype.ext (Category.comp_id x.1)
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint) = G.nsmul t n (schemeHomOverComp x.1 x.2
    idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h
  exact (congrArg Subtype.val h).symm

theorem baseChange_schemeNsmul_comp_fst_and_eq_pullback_map_aux (G : RelativeGroupLaw R f) (n : ℕ) :
    (G.baseChange ι).schemeNsmul n ≫ pullback.fst f ι = pullback.fst f ι ≫ G.schemeNsmul n ∧
    (G.baseChange ι).schemeNsmul n ≫ pullback.snd f ι = pullback.snd f ι ∧
    (G.baseChange ι).schemeNsmul n =
      pullback.map f ι f ι (G.schemeNsmul n) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, G.schemeNsmul_over])
        (by rw [Category.comp_id, Category.id_comp]) := by
  have h1 : (G.baseChange ι).schemeNsmul n ≫ pullback.fst f ι = pullback.fst f ι ≫ G.schemeNsmul n
    := by
    change ((G.baseChange ι).nsmul (baseChangeStr ι f) n idPoint).1 ≫ _ = _
    rw [baseChange_nsmul, baseChangePointOfBase_coe, pullback.lift_fst,
      nsmul_coe_eq_comp_schemeNsmul,
      baseChangePointToBase_coe]
    simp only [Category.id_comp]
  have h2 : (G.baseChange ι).schemeNsmul n ≫ pullback.snd f ι = pullback.snd f ι :=
    (G.baseChange ι).schemeNsmul_over n
  refine ⟨h1, h2, ?_⟩
  apply pullback.hom_ext
  · rw [pullback.lift_fst, h1]
  · rw [pullback.lift_snd, h2, Category.comp_id]

end GoodReductionJacobian.RelativeGroupLaw

theorem
  _root_.GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) :
    (G.baseChange ι).schemeNsmul n ≫ pullback.fst f ι = pullback.fst f ι ≫ G.schemeNsmul n ∧
    (G.baseChange ι).schemeNsmul n ≫ pullback.snd f ι = pullback.snd f ι ∧
    (G.baseChange ι).schemeNsmul n =
      pullback.map f ι f ι (G.schemeNsmul n) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, G.schemeNsmul_over])
        (by rw [Category.comp_id, Category.id_comp]) :=
  GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map_aux ι
    G n
end RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
