/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.PuncturedSpectrumDirectedRefinement

/-!
# Finite-etale descent over the directed punctured-spectrum cover

A cartesian scheme diagram over the directed finite principal-open cover is
already effective by relative gluing.  This file proves that when its chart
maps are finite etale, the resulting glued morphism is finite etale as well.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]

/- A cartesian diagram of finite-etale morphisms on the directed principal
cover glues to a finite-etale morphism over the punctured spectrum. -/
theorem isFiniteEtale_toBase_of_puncturedSpectrumRelativeGluingData
    (d : Cover.RelativeGluingData
      (puncturedSpectrumDirectedOpenCover R))
    (hfinite : ∀ s, IsFiniteEtale (d.natTrans.app s)) :
    IsFiniteEtale d.toBase := by
  let : IsZariskiLocalAtTarget (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance |>.1
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (puncturedSpectrumDirectedOpenCover R)]
  intro s
  change IsFiniteEtale
    (pullback.snd d.toBase
      ((puncturedSpectrumDirectedOpenCover R).f s))
  let h := (d.isPullback_natTrans_ι_toBase s).flip
  have hinv : IsFiniteEtale h.isoPullback.inv := by constructor
  have hfactor : pullback.snd d.toBase
      ((puncturedSpectrumDirectedOpenCover R).f s) =
        h.isoPullback.inv ≫ d.natTrans.app s :=
    (h.isoPullback.inv_hom_id_assoc
      (pullback.snd d.toBase ((puncturedSpectrumDirectedOpenCover R).f s))).symm.trans
        (congrArg (fun k => h.isoPullback.inv ≫ k) h.isoPullback_hom_snd)
  rw [hfactor]
  exact MorphismProperty.IsStableUnderComposition.comp_mem
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
    h.isoPullback.inv (d.natTrans.app s) hinv (hfinite s)

/-- The finite-etale cover obtained from an actual cartesian finite-etale
diagram on the directed principal-open cover. -/
def finiteEtaleOfPuncturedSpectrumRelativeGluingData
    (d : Cover.RelativeGluingData
      (puncturedSpectrumDirectedOpenCover R))
    (hfinite : ∀ s, IsFiniteEtale (d.natTrans.app s)) :
    FiniteEtale (puncturedSpectrum R) :=
  ⟨Over.mk d.toBase,
    isFiniteEtale_toBase_of_puncturedSpectrumRelativeGluingData R d hfinite⟩

end AlgebraicGeometry.Scheme

end
