/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.Descent.RepresentableMatching
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# A compatible global representation after effective descent

The descended universal element is retained explicitly. Consequently its classifying
equivalence agrees with the fixed local representation, a fact needed to compare
group laws rather than merely isomorphism classes of representing objects.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace AlgebraicGeometry.DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
  (G : (Over S)ᵒᵖ ⥤ Type (u + 1))

theorem isSheafFor_coverT_of_isRepresentable
    [G.IsRepresentable] [Flat s] [Surjective s] [QuasiCompact s] (T : Over S) :
    Presieve.IsSheafFor G (Presieve.singleton (coverT s T)) := by
  apply (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fpqcTopology.over S) G).isSheafFor
  rw [← Presieve.ofArrows_pUnit.{0}, ← Sieve.ofArrows,
    GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows,
    Sieve.ofArrows, Presieve.ofArrows_pUnit.{0}]
  exact Precoverage.generate_mem_toGrothendieck
    (pullback.fst T.hom s).singleton_mem_fpqcPrecoverage

variable {X' : Scheme.{u}} (x' : X' ⟶ S')
  (hX' : ((Over.map s).op ⋙ G).RepresentableBy (Over.mk x'))
  {X : Scheme.{u}} (f : X ⟶ S) (e : pullback f s ≅ X')
  (he : e.hom ≫ x' = pullback.snd f s)
  (hG : ∀ T : Over S, Presieve.IsSheafFor G (Presieve.singleton (coverT s T)))
  (hc : eRel s x' f e he ≫ repAct s G x' hX' = (canonical s f).act ≫ e.hom)

/-- The actual descent of the local universal presheaf element. -/
def globalUniversal : G.obj (op (Over.mk f)) :=
  (existsUnique_univX s G x' hX' f e he (hG (Over.mk f)) hc).choose

theorem globalUniversal_spec :
    G.map (cover s f).op (globalUniversal s G x' hX' f e he hG hc) =
      univBC s G x' hX' f e he :=
  (existsUnique_univX s G x' hX' f e he (hG (Over.mk f)) hc).choose_spec.1

variable [∀ T : Over S, EffectiveEpi (pullback.fst T.hom s)]

/-- The global representation whose universal element is the actual descended one. -/
def globalRepresentation : G.RepresentableBy (Over.mk f) where
  homEquiv {T} :=
    Equiv.ofBijective (fun m => G.map m.op (globalUniversal s G x' hX' f e he hG hc))
      ⟨fun _ _ h => map_ζ_injective s G x' hX' f e he
          (globalUniversal s G x' hX' f e he hG hc)
          (globalUniversal_spec s G x' hX' f e he hG hc) h,
        fun z => map_ζ_surjective s G x' hX' f e he
          (globalUniversal s G x' hX' f e he hG hc)
          (globalUniversal_spec s G x' hX' f e he hG hc) hc (hG T).isSeparatedFor z⟩
  homEquiv_comp g m := by
    change G.map (g ≫ m).op _ = G.map g.op (G.map m.op _)
    rw [op_comp, G.map_comp, types_comp_apply]

theorem globalRepresentation_localPoint {T : Over S} (m : T ⟶ Over.mk f) :
    G.map (coverT s T).op
        ((globalRepresentation s G x' hX' f e he hG hc).homEquiv m) =
      localPoint s G x' hX' f e he m :=
  map_coverT_map_eq_homEquiv_bc s G x' hX' f e he
    (globalUniversal s G x' hX' f e he hG hc)
    (globalUniversal_spec s G x' hX' f e he hG hc) m

end AlgebraicGeometry.DescentAction
