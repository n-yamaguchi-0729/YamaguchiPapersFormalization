/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.ExtensionByZero
import EtaleCohomology.Sites.StalkAdjunction
import EtaleCohomology.Sites.Stalks
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Stalks and exactness of extension by zero

For an open immersion, a geometric lift through an étale scheme over the open
subscheme is already a lift over that subscheme. This gives the fiber comparison
used by the general site result in `Sites.StalkAdjunction`.

The stalk of extension by zero agrees with the original stalk inside the open
subscheme and vanishes outside it. Geometric stalks then prove preservation of
short exact sequences and finite limits. The schemes and commutative coefficient
ring are arbitrary; no base field or finiteness hypothesis is used.

Reference: https://stacks.math.columbia.edu/tag/03S2
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)

private def openGeometricFiberEquiv (V : U.Etale) :
    (Scheme.pointSmallEtale (s ≫ j)).fiber.obj ((openEtaleInclusion j).obj V) ≃
      (Scheme.pointSmallEtale s).fiber.obj V where
  toFun a := CategoryTheory.Over.homMk a.left (by
    apply (cancel_mono j).mp
    exact (Category.assoc _ _ _).trans (CategoryTheory.Over.w a))
  invFun b := CategoryTheory.Over.homMk b.left
    ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ j) (CategoryTheory.Over.w b)))
  left_inv a := CategoryTheory.Over.OverMorphism.ext rfl
  right_inv b := CategoryTheory.Over.OverMorphism.ext rfl

/-- Restriction of the geometric fiber at an image point is the original geometric fiber. -/
def openGeometricFiberIso :
    openEtaleInclusion j ⋙ (Scheme.pointSmallEtale (s ≫ j)).fiber ≅
      (Scheme.pointSmallEtale s).fiber :=
  NatIso.ofComponents (fun V => (openGeometricFiberEquiv j s V).toIso) (by
    intro V W f
    ext a
    rfl)

variable (R : Type u) [CommRing R]

/-- Inside the open subscheme, extension by zero has the original geometric stalk. -/
def etaleExtensionByZeroStalkIso :
    etaleExtensionByZero j R ⋙ (Scheme.pointSmallEtale (s ≫ j)).sheafFiber ≅
      (Scheme.pointSmallEtale s).sheafFiber :=
  Sites.adjunctionStalkIso (openEtaleInclusion j) (ModuleCat.{u} R)
    (Scheme.pointSmallEtale (s ≫ j)) (Scheme.pointSmallEtale s)
    (openGeometricFiberIso j s) (etaleExtensionByZero j R)
    ((etaleExtensionByZeroAdjunction j R).ofNatIsoRight
      (etalePullbackOpenRestrictionIso j R))

/-- A geometric point with no lift to the open subscheme has zero stalk after extension. -/
lemma etaleExtensionByZero_stalk_isZero (t : Spec (.of Ω) ⟶ X)
    (h : ∀ r : Spec (.of Ω) ⟶ U, r ≫ j ≠ t)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} R)) :
    IsZero ((Scheme.pointSmallEtale t).sheafFiber.obj ((etaleExtensionByZero j R).obj F)) :=
  Sites.adjunctionStalk_isZero (openEtaleInclusion j) (ModuleCat.{u} R)
    (Scheme.pointSmallEtale t) (etaleExtensionByZero j R)
    ((etaleExtensionByZeroAdjunction j R).ofNatIsoRight
      (etalePullbackOpenRestrictionIso j R))
    (fun V => ⟨fun a => h (a.left ≫ V.hom)
      ((Category.assoc _ _ _).trans (CategoryTheory.Over.w a))⟩) F

/-- Extension by zero preserves short exact sequences of coefficient sheaves. -/
lemma etaleExtensionByZero_shortExact
    (S : ShortComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u} R)))
    (hS : S.ShortExact) : (S.map (etaleExtensionByZero j R)).ShortExact := by
  classical
  apply (shortExact_iff_residueStalk X R _).mpr
  intro x
  let tx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  change (S.map (etaleExtensionByZero j R ⋙ (Scheme.pointSmallEtale tx).sheafFiber)).ShortExact
  by_cases h : ∃ r : Spec (.of (SeparableClosure (X.residueField x))) ⟶ U, r ≫ j = tx
  · obtain ⟨r, hr⟩ := h
    rw [← hr]
    exact ShortComplex.shortExact_of_iso
      (S.mapNatIso (etaleExtensionByZeroStalkIso j r R).symm)
      (hS.map_of_exact (Scheme.pointSmallEtale r).sheafFiber)
  · have hn : ∀ r : Spec (.of (SeparableClosure (X.residueField x))) ⟶ U, r ≫ j ≠ tx :=
      fun r hr => h ⟨r, hr⟩
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _
          (etaleExtensionByZero_stalk_isZero j R tx hn S.X₂)
        mono_f := (etaleExtensionByZero_stalk_isZero j R tx hn S.X₁).mono _
        epi_g := (etaleExtensionByZero_stalk_isZero j R tx hn S.X₃).epi _ }

/-- The stalk vanishes at a geometric point outside the image of the open immersion. -/
lemma etaleExtensionByZero_stalk_isZero_of_not_mem_range
    (t : Spec (.of Ω) ⟶ X) (z : Spec (.of Ω)) (hz : t z ∉ Set.range j)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} R)) :
    IsZero ((Scheme.pointSmallEtale t).sheafFiber.obj ((etaleExtensionByZero j R).obj F)) := by
  apply etaleExtensionByZero_stalk_isZero j R t _ F
  intro r hr
  apply hz
  refine ⟨r z, ?_⟩
  exact congrArg (fun f : Spec (.of Ω) ⟶ X => f z) hr

instance etaleExtensionByZero_additive : (etaleExtensionByZero j R).Additive := by
  let : PreservesBinaryBiproducts (etaleExtensionByZero j R) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts (etaleExtensionByZero j R)
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts (etaleExtensionByZero j R)

instance etaleExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (etaleExtensionByZero j R) := by
  apply (CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (etaleExtensionByZero j R)).mpr
  intro S hS
  have h := etaleExtensionByZero_shortExact j R S hS
  exact ⟨h.exact, h.mono_f⟩

end EtaleCohomology
