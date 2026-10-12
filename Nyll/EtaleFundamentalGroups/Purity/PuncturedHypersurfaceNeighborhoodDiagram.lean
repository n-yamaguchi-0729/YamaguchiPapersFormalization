/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.Order.Directed
import Mathlib.Order.OrderDual
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The actual neighbourhood diagram of a punctured hypersurface

The indices are opens inside the punctured local spectrum that contain its
hypersurface. Their order is reversed so that intersections are later
stages. The cone vertex is the actual pullback of the hypersurface to the
puncture. Its maps to every neighbourhood are constructed using the unique
isomorphism between the corresponding open subschemes of the hypersurface.

Thus no comparison map, pullback identification, or limiting property is
assumed in the neighbourhood system used in Stacks Project, Tag 0BLN.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.PuncturedHypersurface

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] (f : R)

/-- The actual principal closed immersion into the local spectrum. -/
def hypersurfaceMap : Spec (.of (R ⧸ Ideal.span {f})) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))

/-- The hypersurface in the punctured spectrum, defined by its actual pullback. -/
abbrev puncture : Scheme.{u} :=
  Limits.pullback (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f)

/-- The open neighbourhoods of the punctured hypersurface within the puncture. -/
def Neighborhood : Type u :=
  {W : (Spec (.of R)).Opens //
    W ≤ Scheme.puncturedSpectrumOpen R ∧
      ∀ p : PrimeSpectrum R,
        p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ W}

instance : PartialOrder (Neighborhood R f) := inferInstanceAs (PartialOrder (Subtype _))

instance : Nonempty (Neighborhood R f) :=
  ⟨⟨Scheme.puncturedSpectrumOpen R, le_rfl, fun _ hp _ ↦ hp⟩⟩

instance : IsDirectedOrder (OrderDual (Neighborhood R f)) where
  directed W V := by
    let D : Neighborhood R f :=
      ⟨W.val ⊓ V.val, inf_le_left.trans W.property.1,
        fun p hp hfp ↦ ⟨W.property.2 p hp hfp, V.property.2 p hp hfp⟩⟩
    refine ⟨OrderDual.toDual D, ?_, ?_⟩
    · change W.val ⊓ V.val ≤ W.val
      exact inf_le_left
    · change W.val ⊓ V.val ≤ V.val
      exact inf_le_right

/-- Pulling a neighbourhood back to the hypersurface gives exactly its puncture. -/
theorem preimage_neighborhood_eq (W : Neighborhood R f) :
    hypersurfaceMap R f ⁻¹ᵁ W.val =
      hypersurfaceMap R f ⁻¹ᵁ Scheme.puncturedSpectrumOpen R := by
  ext z
  constructor
  · intro hz
    exact W.property.1 hz
  · intro hz
    apply W.property.2 (hypersurfaceMap R f z) hz
    change Ideal.Quotient.mk (Ideal.span {f}) f ∈ z.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
    exact z.asIdeal.zero_mem

private theorem neighborhoodPullback_range_eq (W : Neighborhood R f) :
    Set.range (Limits.pullback.snd
      (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f)) =
        Set.range (Limits.pullback.snd W.val.ι (hypersurfaceMap R f)) := by
  rw [IsOpenImmersion.range_pullbackSnd, IsOpenImmersion.range_pullbackSnd,
    Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
  exact congrArg (fun V : (Spec (.of (R ⧸ Ideal.span {f}))).Opens ↦
    (V : Set (Spec (.of (R ⧸ Ideal.span {f})))))
    (preimage_neighborhood_eq R f W).symm

/-- The actual hypersurface pullback over each neighbourhood is the same open
subscheme of the hypersurface as the original puncture. -/
def neighborhoodPullbackIso (W : Neighborhood R f) :
    puncture R f ≅ Limits.pullback W.val.ι (hypersurfaceMap R f) :=
  IsOpenImmersion.isoOfRangeEq
    (Limits.pullback.snd (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f))
    (Limits.pullback.snd W.val.ι (hypersurfaceMap R f))
    (neighborhoodPullback_range_eq R f W)

/-- The hypersurface comparison preserves its map to the closed hypersurface. -/
theorem neighborhoodPullbackIso_hom_snd (W : Neighborhood R f) :
    (neighborhoodPullbackIso R f W).hom ≫
        Limits.pullback.snd W.val.ι (hypersurfaceMap R f) =
      Limits.pullback.snd (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac
    (Limits.pullback.snd (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f))
    (Limits.pullback.snd W.val.ι (hypersurfaceMap R f))
    (neighborhoodPullback_range_eq R f W)

/-- The punctured hypersurface maps canonically into every neighbourhood. -/
def projection (W : Neighborhood R f) : puncture R f ⟶ W.val.toScheme :=
  (neighborhoodPullbackIso R f W).hom ≫
    Limits.pullback.fst W.val.ι (hypersurfaceMap R f)

/-- Each projection is over the original local spectrum. -/
theorem projection_comp_ι (W : Neighborhood R f) :
    projection R f W ≫ W.val.ι =
      Limits.pullback.fst (Scheme.puncturedSpectrumOpen R).ι (hypersurfaceMap R f) ≫
        (Scheme.puncturedSpectrumOpen R).ι := by
  change ((neighborhoodPullbackIso R f W).hom ≫
    Limits.pullback.fst W.val.ι (hypersurfaceMap R f)) ≫ W.val.ι = _
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
    neighborhoodPullbackIso_hom_snd]
  exact Limits.pullback.condition.symm

/-- The inverse diagram consists of the actual open subschemes and inclusions. -/
def diagram : (OrderDual (Neighborhood R f))ᵒᵖ ⥤ Scheme.{u} where
  obj W := W.unop.val.toScheme
  map h := (Spec (.of R)).homOfLE (leOfHom h.unop)
  map_id W := (Spec (.of R)).homOfLE_rfl W.unop.val
  map_comp h k := ((Spec (.of R)).homOfLE_homOfLE
    (leOfHom h.unop) (leOfHom k.unop)).symm

/-- The canonical cone with vertex the actual punctured hypersurface. -/
def cone : Cone (diagram R f) where
  pt := puncture R f
  π :=
    { app W := projection R f W.unop
      naturality {W V} h := by
        change 𝟙 (puncture R f) ≫ projection R f V.unop =
          projection R f W.unop ≫ (Spec (.of R)).homOfLE (leOfHom h.unop)
        rw [Category.id_comp]
        apply (cancel_mono V.unop.val.ι).1
        rw [Category.assoc, Scheme.homOfLE_ι]
        exact (projection_comp_ι R f V.unop).trans
          (projection_comp_ι R f W.unop).symm }

end AlgebraicGeometry.FiniteEtale.PuncturedHypersurface
