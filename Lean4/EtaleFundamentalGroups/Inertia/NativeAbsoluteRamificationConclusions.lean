/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeAbsoluteRamificationDiagram
import ProCGroups.ProC.InverseLimits.Predicates
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Every conclusion of the absolute DVR ramification theorem

This OUTPUT certificate includes literal residue algebraic and separable
closures, the full invertible exponent index, both original exact sequences,
normality and the complete pro-p/characteristic-zero laws for the SAME P.
Its continuous character and quotient isomorphism have the intrinsic full
separable roots target. Equivariance uses the residue action computed from
the SAME map in the first exact sequence. The original-input theorem
constructs this certificate; no conclusion is an input assumption.
-/

namespace EtaleFundamentalGroups.Inertia

universe u w

attribute [local instance] NativeAbsoluteRamificationGroups.inertiaTopology
  NativeAbsoluteRamificationGroups.tameQuotientTopology

/-- All original conclusions of Stacks Project Tag 0BUB on the displayed actual data. -/
structure NativeAbsoluteRamificationConclusions
    (R : NativeAbsoluteRamificationResidues.{u, w}) (G : NativeAbsoluteRamificationGroups.{w})
    (D : NativeAbsoluteRamificationDiagram R G) : Prop where
  /-- The literal residue closure and the exact full exponent index. -/
  residue_closure : NativeAbsoluteResidueConclusions R
  /-- The first sequence starts with the original injective inertia inclusion. -/
  inertia_inclusion_injective : Function.Injective G.inertiaInclusion.hom'.toFun
  /-- Its inertia image is exactly the kernel of the SAME absolute residue map. -/
  residue_kernel : D.residueMorphism.hom'.ker = G.inertiaInclusion.hom'.range
  /-- The SAME original absolute residue map is onto Gal(κsep/κ). -/
  residue_surjective : Function.Surjective D.residueMorphism.hom'.toFun
  /-- The second sequence starts with the literal inclusion of independent P. -/
  wild_inclusion_injective : Function.Injective G.wild.subtype.toFun
  /-- That SAME P is normal in original D. -/
  wild_normal_in_decomposition : (G.wild.map G.inertiaInclusion.hom').Normal
  /-- Pro-p includes its original profinite topology and finite-p quotient basis. -/
  wild_pro_p : ∀ (p : ℕ) [Fact p.Prime] [CharP R.baseResidue.α p],
    let : Group (Subtype G.wild.carrier) := Subgroup.toGroup G.wild
    let : TopologicalSpace (Subtype G.wild.carrier) :=
      TopologicalSpace.induced
        (fun σ : Subtype G.wild.carrier => (show G.inertia.carrier from σ.val))
        G.inertiaTopology
    CompactSpace (Subtype G.wild.carrier) ∧
      T2Space (Subtype G.wild.carrier) ∧
      TotallyDisconnectedSpace (Subtype G.wild.carrier) ∧
      IsTopologicalGroup (Subtype G.wild.carrier) ∧
      ProCGroups.ProC.HasPGroupOpenNormalBasis p (Subtype G.wild.carrier)
  /-- The SAME independently defined wild subgroup is trivial in characteristic zero. -/
  wild_char_zero : ∀ [CharZero R.baseResidue.α], G.wild = ⊥
  /-- The canonical character into the literal full root limit is continuous. -/
  character_continuous : Continuous D.character.hom'.toFun
  /-- It reaches every compatible family on ALL residue-invertible exponents. -/
  character_surjective : Function.Surjective D.character.hom'.toFun
  /-- Its kernel is the SAME independently defined P. -/
  character_kernel : D.character.hom'.ker = G.wild
  /-- Original conjugation corresponds to the SAME original absolute residue action. -/
  character_equivariant : ∀ (d : G.decomposition.carrier) (σ : G.inertia.carrier),
    D.character.hom'.toFun (G.conjugate d σ) = D.rootsAction d (D.character.hom'.toFun σ)
  /-- The SAME original quotient map is onto. -/
  quotient_surjective : Function.Surjective G.quotientProjection.hom'.toFun
  /-- The SAME original quotient map has exactly P as kernel. -/
  quotient_kernel : G.quotientProjection.hom'.ker = G.wild
  /-- The canonical character induces the continuous group isomorphism from the SAME I/P. -/
  quotient_isomorphism : ∃ e : G.tameQuotient.carrier ≃ₜ* R.rootsGroup.carrier,
    ∀ σ : G.inertia.carrier,
      e.toMulEquiv.toFun (G.quotientProjection.hom'.toFun σ) = D.character.hom'.toFun σ

end EtaleFundamentalGroups.Inertia
