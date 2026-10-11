/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Translation
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationCover
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup

/-!
# Torsion translations of multiplication covers

Translation by an actual torsion section preserves the multiplication morphism.
Its inverse is translation by the inverse section, so it gives an automorphism
of the actual finite étale multiplication cover. On relative scheme points its
action is the original group law, with no comparison of actions assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom.S17Glue
open RelativeGroupLaw_surjective_schemeNsmul_of_flat_of_field.GoodReductionJacobian.RelativeGroupLaw
  (nsmul_mul)

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f)

/-- Evaluation of translation on any relative point is multiplication by the
same section pulled back to the test scheme. -/
theorem point_comp_translate {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver s f) (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) :
    x.1 ≫ G.translate t =
      (G.mul s x (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) t)).1 := by
  let u : SchemeHomOver f f :=
    GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) t
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (idPoint : SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id x.1)
  have hu : GoodReductionJacobian.schemeHomOverComp x.1 x.2 u =
      GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) t := by
    apply Subtype.ext
    change x.1 ≫ (f ≫ t.1) = s ≫ t.1
    rw [← Category.assoc, x.2]
  have h := G.mul_natural f s x.1 x.2 idPoint u
  rw [hx, hu] at h
  exact congrArg Subtype.val h

/-- Composition of two translations is translation by their product. -/
theorem translate_comp_translate
    (t u : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) :
    G.translate t ≫ G.translate u = G.translate (G.mul (𝟙 _) t u) := by
  rw [G.point_comp_translate f ⟨G.translate t, G.translate_over t⟩ u]
  change (G.mul f
      (G.mul f idPoint (GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) t))
      (GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) u)).1 =
    (G.mul f idPoint
      (GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) (G.mul (𝟙 _) t u))).1
  rw [G.mul_assoc, G.mul_natural]

/-- Translation is an actual scheme isomorphism, with inverse translation by
the inverse section. -/
def translateIso (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) : A ≅ A where
  hom := G.translate t
  inv := G.translate (G.inv (𝟙 _) t)
  hom_inv_id := by
    rw [G.translate_comp_translate, G.mul_inv_cancel, G.translate_one]
  inv_hom_id := by
    rw [G.translate_comp_translate, G.inv_mul_cancel, G.translate_one]

/-- Translation by an actual `n`-torsion section preserves the actual `[n]` map. -/
theorem translate_comp_schemeNsmul (hc : G.IsCommutative) (n : ℕ)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
    (ht : G.IsTorsionPoint (𝟙 _) n t) :
    G.translate t ≫ G.schemeNsmul n = G.schemeNsmul n := by
  let u : SchemeHomOver f f :=
    GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) t
  have hu : G.nsmul f n u = G.one f :=
    G.isTorsionPoint_schemeHomOverComp (𝟙 _) f f (Category.comp_id f) n ht
  change (G.mul f idPoint u).1 ≫ G.schemeNsmul n = _
  rw [← nsmul_coe_eq_comp_schemeNsmul G n (G.mul f idPoint u)]
  have hm := nsmul_mul G hc f n idPoint u
  rw [hm, hu, G.mul_one]
  rfl

/-- A torsion translation gives a deck automorphism of the actual finite étale
multiplication cover. -/
def multiplicationCoverTranslation (hc : G.IsCommutative) [CharZero K]
    [IsProper f] [Smooth f] (n : ℕ+)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
    (ht : G.IsTorsionPoint (𝟙 _) (n : ℕ) t) :
    Aut (G.multiplicationCover hc n) :=
  MorphismProperty.Over.isoMk (G.translateIso t)
    (G.translate_comp_schemeNsmul hc (n : ℕ) t ht)

/-- The underlying scheme map of the deck automorphism is the original
translation morphism. -/
theorem multiplicationCoverTranslation_hom_left (hc : G.IsCommutative) [CharZero K]
    [IsProper f] [Smooth f] (n : ℕ+)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
    (ht : G.IsTorsionPoint (𝟙 _) (n : ℕ) t) :
    (G.multiplicationCoverTranslation hc n t ht).hom.left = G.translate t := rfl

/-- On the actual underlying scheme points, a torsion deck translation acts
by the original group law. This computes its action before any fibre-to-torsion
comparison is applied. -/
theorem point_comp_multiplicationCoverTranslation (hc : G.IsCommutative) [CharZero K]
    [IsProper f] [Smooth f] (n : ℕ+)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
    (ht : G.IsTorsionPoint (𝟙 _) (n : ℕ) t)
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver s f) :
    x.1 ≫ (G.multiplicationCoverTranslation hc n t ht).hom.left =
      (G.mul s x (GoodReductionJacobian.schemeHomOverComp s (Category.comp_id s) t)).1 :=
  G.point_comp_translate s x t

/-- The point of the original group scheme underlying an actual geometric
point in a multiplication-cover fibre. -/
def multiplicationFiberPoint (hc : G.IsCommutative) [CharZero K]
    [IsProper f] [Smooth f] {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ A) (n : ℕ+)
    (z : (FiniteEtale.fiber ξ).obj (G.multiplicationCover hc n)) :
    SchemeHomOver (ξ ≫ f) f := by
  let p : Over.mk ξ ⟶ (G.multiplicationCover hc n).toComma :=
    FiniteEtale.fiberObjEquivHom ξ (G.multiplicationCover hc n) z
  let q : Spec (CommRingCat.of Ω) ⟶ A := p.left
  have hq : q ≫ G.schemeNsmul (n : ℕ) = ξ := Over.w p
  refine ⟨q, ?_⟩
  calc
    q ≫ f = q ≫ (G.schemeNsmul (n : ℕ) ≫ f) :=
      congrArg (fun r : A ⟶ Spec (CommRingCat.of K) => q ≫ r)
        (G.schemeNsmul_over (n : ℕ)).symm
    _ = (q ≫ G.schemeNsmul (n : ℕ)) ≫ f :=
      (Category.assoc q (G.schemeNsmul (n : ℕ)) f).symm
    _ = ξ ≫ f := congrArg (fun r : Spec (CommRingCat.of Ω) ⟶ A => r ≫ f) hq

/-- The action of a torsion deck translation on the actual geometric fibre
is pointwise multiplication by the torsion section. -/
theorem multiplicationFiberPoint_map_translation (hc : G.IsCommutative) [CharZero K]
    [IsProper f] [Smooth f] {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ A) (n : ℕ+)
    (t : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f)
    (ht : G.IsTorsionPoint (𝟙 _) (n : ℕ) t)
    (z : (FiniteEtale.fiber ξ).obj (G.multiplicationCover hc n)) :
    G.multiplicationFiberPoint hc ξ n
        ((FiniteEtale.fiber ξ).map (G.multiplicationCoverTranslation hc n t ht).hom z) =
      G.mul (ξ ≫ f) (G.multiplicationFiberPoint hc ξ n z)
        (GoodReductionJacobian.schemeHomOverComp (ξ ≫ f) (Category.comp_id (ξ ≫ f)) t) := by
  apply Subtype.ext
  have h := FiniteEtale.fiberObjEquivHom_naturality ξ
    (G.multiplicationCoverTranslation hc n t ht).hom z
  have hleft := congrArg
    (fun q : Over.mk ξ ⟶ (G.multiplicationCover hc n).toComma => q.left) h.symm
  exact hleft.trans (G.point_comp_translate (ξ ≫ f)
    (G.multiplicationFiberPoint hc ξ n z) t)

end GoodReductionJacobian.RelativeGroupLaw
