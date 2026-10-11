/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_PolarisedAbelianScheme.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Topology.KrullDimension
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.ProjectivePresentation

/-!
# Polarised Abelian Scheme
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GoodReductionJacobian.RelativeGroupLaw

/-- The finite product of relative points with the specified natural-number exponents. -/
def finComb {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) {m : ℕ}
    (x : Fin m → SchemeHomOver t f) (c : Fin m → ℕ) : SchemeHomOver t f :=
  letI := L.pointGroup t
  (List.ofFn fun i => x i ^ c i).prod

end GoodReductionJacobian.RelativeGroupLaw

namespace AlgebraicGeometry

/-- The rank of global sections of the sheaf on the specified geometric fibre. -/
def Scheme.Modules.geomFibreH0Finrank {S : Type u} [CommRing S] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (M : A.Modules) (k : Type u) [Field k] (sk : S →+* k) : ℕ :=
  letI : Algebra k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom
    sk)))).obj M, ⊤) :=
    Module.compHom _ (algebraMap k Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)), ⊤))
  Module.finrank k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom
    sk)))).obj M, ⊤)

/-- An abelian scheme with level structure and a chosen very ample polarisation. -/
structure PolarisedAbelianScheme (g d n : ℕ) (S : Type u) [CommRing S] : Type (u + 1) where
  /-- The total space of the abelian scheme. -/
  A : Scheme.{u}
  /-- The structure morphism to the base spectrum. -/
  f : A ⟶ Spec (CommRingCat.of S)
  /-- The relative group law on the total space. -/
  L : RelativeGroupLaw S f
  /-- Commutativity of the relative group law. -/
  comm : L.IsCommutative
  /-- The geometric properties required of an abelian scheme. -/
  bundle : AbelianSchemePropertyBundle S f
  /-- Each fibre has the specified dimension. -/
  dim_fibre : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g
  /-- The chosen sections defining the level structure. -/
  P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f
  /-- The chosen sections are killed by the level integer. -/
  P_torsion : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of
    S)))
  /-- The chosen torsion sections are independent on every geometric fibre. -/
  P_indep : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c c' : Fin (2 * g) → Fin n),
    L.finComb (Spec.map (CommRingCat.ofHom sk))
        (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i))
          (fun i => (c i : ℕ)) =
      L.finComb (Spec.map (CommRingCat.ofHom sk))
        (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i))
          (fun i => (c' i : ℕ)) →
      c = c'
  /-- The chosen torsion sections span the geometric torsion points. -/
  P_span : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (Spec.map
    (CommRingCat.ofHom sk)) f),
    L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
      ∃ c : Fin (2 * g) → Fin n,
        L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P
            i)) (fun i => (c i : ℕ)) = Q
  /-- The sheaf of modules defining the polarisation. -/
  pol : A.Modules
  /-- The polarisation sheaf is invertible. -/
  pol_isInvertible : Scheme.Modules.IsInvertible pol
  /-- Sections of the polarisation define a relative closed immersion. -/
  pol_veryAmple : Scheme.Modules.ClosedImmersionBySections pol f
  /-- The polarisation has the specified rank of sections on geometric fibres. -/
  pol_finrank : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
    Scheme.Modules.geomFibreH0Finrank f pol k sk = d

namespace PolarisedAbelianScheme

variable {g d n : ℕ}

/-- Isomorphism of the group schemes preserving the level sections and local polarisations. -/
def Iso {S : Type u} [CommRing S] (u u' : PolarisedAbelianScheme g d n S) : Prop :=
  ∃ (e : u.A ≅ u'.A) (he : e.hom ≫ u'.f = u.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.f),
      (u.L.mul t x y).1 ≫ e.hom =
        (u'.L.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he]; exact x.2⟩
          ⟨y.1 ≫ e.hom, by rw [Category.assoc, he]; exact y.2⟩).1) ∧
    (∀ i, (u.P i).1 ≫ e.hom = (u'.P i).1) ∧
    (∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj
        u'.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol))

/-- Compatibility of the group law, level sections, and polarisation with base change. -/
def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S') : Prop :=
  ∃ (gA : u'.A ⟶ u.A) (hg : CategoryTheory.IsPullback gA u'.f u.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
    (∀ i, (u'.P i).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1) ∧
    Nonempty ((Scheme.Modules.pullback gA).obj u.pol ≅ u'.pol)

/-- The classification properties of the given map to the proposed moduli scheme. -/
structure IsFineModuli (g d n : ℕ) {B : Type} [CommRing B]
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      PolarisedAbelianScheme g d n S → SchemeHomOver s πM) : Prop where
  /-- Isomorphic polarised abelian schemes determine the same moduli point. -/
  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : PolarisedAbelianScheme g d n S), Iso u u' → pt S s u = pt S s u'
  /-- The classification map is compatible with base change. -/
  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec
      (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S'),
    IsPullback φ u u' → (pt S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s u).1
  /-- Every relative point of the moduli scheme represents an object. -/
  pt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of
    B)) (x : SchemeHomOver s πM),
    ∃ u : PolarisedAbelianScheme g d n S, pt S s u = x
  /-- Objects defining the same moduli point are isomorphic. -/
  pt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : PolarisedAbelianScheme g d n S), pt S s u = pt S s u' → Iso u u'

end PolarisedAbelianScheme

end AlgebraicGeometry

end
