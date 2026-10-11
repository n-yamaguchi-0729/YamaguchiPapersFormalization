/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SplitTorusMu.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# Split Torus Mu
-/

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.SplitTorus

/-- The group algebra giving coordinates on a product of group schemes of roots of unity. -/
abbrev muCoord (S : Type u) [CommRing S] (t m : ℕ) : Type u := AddMonoidAlgebra S (Fin t → ZMod m)

/-- The affine group scheme with character group `Fin t → ZMod m`. -/
abbrev muScheme (S : Type u) [CommRing S] (t m : ℕ) : Scheme.{u} := Spec (CommRingCat.of (muCoord S
  t m))

/-- The structure morphism of the product of group schemes of roots of unity. -/
abbrev muStr (S : Type u) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (muCoord S t m)))

/-- The Laurent group algebra giving coordinates on the split torus. -/
abbrev torusCoord (S : Type u) [CommRing S] (t : ℕ) : Type u := AddMonoidAlgebra S (Fin t → ℤ)

/-- The split torus with character lattice `Fin t → ℤ`. -/
abbrev torusScheme (S : Type u) [CommRing S] (t : ℕ) : Scheme.{u} := Spec (CommRingCat.of
  (torusCoord S t))

/-- The structure morphism of the split torus. -/
abbrev torusStr (S : Type u) [CommRing S] (t : ℕ) : torusScheme S t ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t)))

/-- The natural morphism from the product of groups of roots of unity into the split torus. -/
abbrev muToTorus (S : Type u) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t =>
      ℤ) i))))

/-- The inclusion of groups of roots of unity induced by divisibility of their orders. -/
abbrev muIncl (S : Type u) [CommRing S] (t : ℕ) {m m' : ℕ} (h : m ∣ m') : muScheme S t m ⟶ muScheme
  S t m' :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => ((ZMod.castHom h (ZMod m)).toAddMonoidHom).comp
      (Pi.evalAddMonoidHom (fun _ : Fin t => ZMod m') i))))

/-- The morphism on groups of roots of unity induced by a change of coefficient ring. -/
abbrev muBaseChange {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (t m : ℕ) :
    muScheme S' t m ⟶ muScheme S t m :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) φ))

/-- The morphism on split tori induced by a change of coefficient ring. -/
abbrev torusBaseChange {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (t : ℕ) :
    torusScheme S' t ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) φ))

/--
The point over an extension algebra defined by an algebra homomorphism from the roots-of-unity
coordinate ring.
-/
def muPt (S S' : Type u) [CommRing S] [CommRing S'] [Algebra S S'] (t m : ℕ) (χ : muCoord S t m
  →ₐ[S] S') :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) (muStr S t m) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact χ.comp_algebraMap⟩

/-- The point of the split torus defined by an algebra homomorphism from its coordinate ring. -/
def torusPt (S S' : Type u) [CommRing S] [CommRing S'] [Algebra S S'] (t : ℕ) (χ : torusCoord S t
  →ₐ[S] S') :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) (torusStr S t) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact χ.comp_algebraMap⟩

/--
The point of the split torus over the identity base map defined by a coordinate algebra
homomorphism.
-/
def torusPtId (S : Type u) [CommRing S] (t : ℕ) (χ : torusCoord S t →ₐ[S] S) : SchemeHomOver (𝟙 _)
  (torusStr S t) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χ.toRingHom.comp (algebraMap S (torusCoord S t)) = RingHom.id S := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]⟩

/--
The point of the roots-of-unity group over the identity base map defined by a coordinate algebra
homomorphism.
-/
def muPtId (S : Type u) [CommRing S] (t m : ℕ) (χ : muCoord S t m →ₐ[S] S) : SchemeHomOver (𝟙 _)
  (muStr S t m) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χ.toRingHom.comp (algebraMap S (muCoord S t m)) = RingHom.id S := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]⟩

end AlgebraicGeometry.SplitTorus

end
