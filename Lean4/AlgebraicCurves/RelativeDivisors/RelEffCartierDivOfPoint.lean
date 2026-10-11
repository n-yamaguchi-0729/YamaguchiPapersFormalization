/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelEffCartierDivOfPoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv

/-!
# Relative divisors defined by sections

Constructs the divisor associated to the graph of a section over the base.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S}

/-- The graph of a morphism over the base, regarded as a section of the pullback. -/
noncomputable def graphOver (a : T ⟶ 𝒞) (ha : a ≫ f = g) : T ⟶ pullback f g :=
  pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm)

lemma graphOver_eq_lift (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha = pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm) := rfl
@[reassoc (attr := simp)]
lemma graphOver_fst (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.fst f g = a :=
  pullback.lift_fst _ _ _
@[reassoc (attr := simp)]
lemma graphOver_snd (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.snd f g = 𝟙 T :=
  pullback.lift_snd _ _ _

instance isClosedImmersion_graphOver [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    IsClosedImmersion (graphOver f a ha) := by
  have : IsClosedImmersion (graphOver f a ha ≫ pullback.snd f g) := by
    rw [graphOver_snd]; infer_instance
  exact .of_comp (graphOver f a ha) (pullback.snd f g)

instance isIso_ker_graphOver_subschemeIota_snd [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    IsIso ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g) := by
  have h : (graphOver f a ha).toImage ≫ ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g)
      = 𝟙 T := by
    rw [← Category.assoc]
    change ((graphOver f a ha).toImage ≫ (graphOver f a ha).imageι) ≫ _ = _
    rw [Scheme.Hom.toImage_imageι, graphOver_snd]
  exact IsIso.of_isIso_fac_left h

/-- The relative effective Cartier divisor of degree one defined by the graph of a point. -/
noncomputable def RelEffCartierDiv.ofPoint [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    RelEffCartierDiv f 1 g where
  I := (graphOver f a ha).ker
  isFinite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance
  finrank_eq t := by
    rw [Scheme.Hom.finrank_eq_one_of_isIso ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g)]
    rfl

@[simp] lemma RelEffCartierDiv.ofPoint_I [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    (RelEffCartierDiv.ofPoint f a ha).I = (graphOver f a ha).ker := rfl

variable {f} in
instance RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one (D : RelEffCartierDiv f 1 g) :
    IsIso (D.I.subschemeι ≫ pullback.snd f g) := by
  have := D.isFinite
  have := D.flat
  exact (Scheme.Hom.isIso_iff_finrank_eq _).mpr (funext fun t => D.finrank_eq t)

variable {f} in
/-- The point determined by a relative effective Cartier divisor of degree one. -/
noncomputable def RelEffCartierDiv.toPoint (D : RelEffCartierDiv f 1 g) : T ⟶ 𝒞 :=
  inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ pullback.fst f g

variable {f} in
@[reassoc (attr := simp)]
lemma RelEffCartierDiv.toPoint_comp (D : RelEffCartierDiv f 1 g) : D.toPoint ≫ f = g := by
  calc D.toPoint ≫ f
      = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ (pullback.fst f g ≫ f) := by
        simp only [RelEffCartierDiv.toPoint, Category.assoc]
    _ = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ (D.I.subschemeι ≫ pullback.snd f g) ≫ g := by
        rw [pullback.condition, Category.assoc]
    _ = g := by rw [IsIso.inv_hom_id_assoc]

end AlgebraicGeometry
