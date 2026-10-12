/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.Normalization

/-!
# Reconstruction of labelled projective configurations

Normalize a reference triple and compare the remaining affine coordinates.
Equal cross ratios then give an explicit projective coordinate equivalence
carrying every label of one configuration to the corresponding label of the other.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u v
variable {K : Type u} [Field K]

/-- The coordinate normalization of three distinct projective points. -/
noncomputable def normalizeTriple (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a) :
    Projectivization K (K × K) ≃ Projectivization K (K × K) :=
  normalizeCoordinates a.rep b.rep c.rep
    (fun h => hab ((bracket_rep_eq_zero_iff a b).mp h))
    (fun h => hcb ((bracket_rep_eq_zero_iff c b).mp h))
    (fun h => hca ((bracket_rep_eq_zero_iff c a).mp h))

/-- The affine coordinate under normalization is the intrinsic cross ratio. -/
theorem normalizeTriple_apply (a b c d : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a) (hdb : d ≠ b) :
    normalizeTriple a b c hab hcb hca d = affinePoint (crossRatio a b c d) := by
  conv_lhs => rw [← d.mk_rep]
  exact normalizeCoordinates_mk a.rep b.rep c.rep d.rep _ _ _ d.rep_nonzero
    (fun h => hdb ((bracket_rep_eq_zero_iff d b).mp h))

/-- The middle reference point is the pole of the normalized affine coordinate. -/
theorem normalizeTriple_second (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a) :
    normalizeTriple a b c hab hcb hca b = infinityPoint := by
  calc
    normalizeTriple a b c hab hcb hca b =
        normalizeTriple a b c hab hcb hca
          (Projectivization.mk K b.rep b.rep_nonzero) :=
      congrArg (normalizeTriple a b c hab hcb hca) b.mk_rep.symm
    _ = infinityPoint :=
      normalizeCoordinates_second a.rep b.rep c.rep _ _ _ b.rep_nonzero

/-- Triple normalization preserves all cross ratios. -/
theorem crossRatio_normalizeTriple (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (w x y z : Projectivization K (K × K)) :
    crossRatio (normalizeTriple a b c hab hcb hca w)
      (normalizeTriple a b c hab hcb hca x)
      (normalizeTriple a b c hab hcb hca y)
      (normalizeTriple a b c hab hcb hca z) = crossRatio w x y z := by
  exact crossRatio_projectiveCoordinateChange _ _ _ _ _ w x y z

/-- Change coordinates by normalizing the source and undoing target normalization. -/
noncomputable def matchTriples (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a') :
    Projectivization K (K × K) ≃ Projectivization K (K × K) :=
  (normalizeTriple a b c hab hcb hca).trans
    (normalizeTriple a' b' c' hab' hcb' hca').symm

/-- The coordinate change matching two triples preserves cross ratios. -/
theorem crossRatio_matchTriples (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a')
    (w x y z : Projectivization K (K × K)) :
    let f := matchTriples a b c a' b' c' hab hcb hca hab' hcb' hca'
    crossRatio (f w) (f x) (f y) (f z) = crossRatio w x y z := by
  dsimp only
  rw [← crossRatio_normalizeTriple a' b' c' hab' hcb' hca']
  change crossRatio
    ((normalizeTriple a' b' c' hab' hcb' hca')
      ((normalizeTriple a' b' c' hab' hcb' hca').symm
        (normalizeTriple a b c hab hcb hca w)))
    ((normalizeTriple a' b' c' hab' hcb' hca')
      ((normalizeTriple a' b' c' hab' hcb' hca').symm
        (normalizeTriple a b c hab hcb hca x)))
    ((normalizeTriple a' b' c' hab' hcb' hca')
      ((normalizeTriple a' b' c' hab' hcb' hca').symm
        (normalizeTriple a b c hab hcb hca y)))
    ((normalizeTriple a' b' c' hab' hcb' hca')
      ((normalizeTriple a' b' c' hab' hcb' hca').symm
        (normalizeTriple a b c hab hcb hca z))) = _
  simp only [Equiv.apply_symm_apply]
  exact crossRatio_normalizeTriple a b c hab hcb hca w x y z

/-- Equal cross ratios determine the image of any point away from the pole. -/
theorem matchTriples_apply (a b c a' b' c' d d' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a')
    (hdb : d ≠ b) (hdb' : d' ≠ b')
    (h : crossRatio a b c d = crossRatio a' b' c' d') :
    matchTriples a b c a' b' c' hab hcb hca hab' hcb' hca' d = d' := by
  apply (normalizeTriple a' b' c' hab' hcb' hca').injective
  change (normalizeTriple a' b' c' hab' hcb' hca')
    ((normalizeTriple a' b' c' hab' hcb' hca').symm
      (normalizeTriple a b c hab hcb hca d)) = _
  rw [Equiv.apply_symm_apply, normalizeTriple_apply a b c d hab hcb hca hdb,
    normalizeTriple_apply a' b' c' d' hab' hcb' hca' hdb', h]

/-- The coordinate matching also carries the pole to the target pole. -/
theorem matchTriples_second (a b c a' b' c' : Projectivization K (K × K))
    (hab : a ≠ b) (hcb : c ≠ b) (hca : c ≠ a)
    (hab' : a' ≠ b') (hcb' : c' ≠ b') (hca' : c' ≠ a') :
    matchTriples a b c a' b' c' hab hcb hca hab' hcb' hca' b = b' := by
  apply (normalizeTriple a' b' c' hab' hcb' hca').injective
  change (normalizeTriple a' b' c' hab' hcb' hca')
    ((normalizeTriple a' b' c' hab' hcb' hca').symm
      (normalizeTriple a b c hab hcb hca b)) = _
  rw [Equiv.apply_symm_apply, normalizeTriple_second, normalizeTriple_second]

/-- A single projective coordinate change matches every label once the cross
ratios relative to three distinct reference labels agree. The index type may
be infinite; no point-by-point choice of coordinate change is made. -/
theorem matchTriples_configuration {ι : Type v}
    (x y : ι → Projectivization K (K × K))
    (hx : Function.Injective x) (hy : Function.Injective y)
    (i₀ iInf i₁ : ι) (hZeroInf : i₀ ≠ iInf) (hOneInf : i₁ ≠ iInf) (h₁₀ : i₁ ≠ i₀)
    (h : ∀ i, crossRatio (x i₀) (x iInf) (x i₁) (x i) =
      crossRatio (y i₀) (y iInf) (y i₁) (y i)) (i : ι) :
    matchTriples (x i₀) (x iInf) (x i₁) (y i₀) (y iInf) (y i₁)
      (hx.ne hZeroInf) (hx.ne hOneInf) (hx.ne h₁₀)
      (hy.ne hZeroInf) (hy.ne hOneInf) (hy.ne h₁₀) (x i) = y i := by
  by_cases hi : i = iInf
  · subst i
    exact matchTriples_second _ _ _ _ _ _ _ _ _ _ _ _
  · exact matchTriples_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hx.ne hi) (hy.ne hi) (h i)

end AnabelianGeometry.ProjectiveLine
