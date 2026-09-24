import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPushTransition
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjVeroneseIso

/-! # The twist comparison map of a graded ring isomorphism is an isomorphism

Statement: let `f : 𝒜 →+*ᵍ ℬ` and `g : ℬ →+*ᵍ 𝒜` be mutually inverse graded ring homomorphisms (`g ∘ f = id`,
`f ∘ g = id`). Then
(1) the transition maps are mutually inverse: `T(f) ≫ T(g) = 𝟙` (`Proj.twistPushTransition`, for any common target `Y`);
(2) the comparison morphism of Stacks 01MX, `θ_f = Proj.twistToPushforward f hf n : O_{Proj 𝒜}(n) ⟶ (Proj.map f)_* O_{Proj ℬ}(n)`,
is an isomorphism;
(3) special case: the `θ` of the graded ring isomorphism `ofVeronese : A(U)^{(m)} → A^{(m)}(U)` (`ProjVeroneseIso`) is an
isomorphism.

This is step 3a of the proof in `VeroneseTwistPullback`.

Sources: Stacks 01MX (θ), 01NP (transitivity of the transition maps).

Proof:
1. `twistPushTransition_comp` (`ProjTwistPushTransition`) rewrites `T(f) ≫ T(g)` as `T(g ∘ f)`; `g ∘ f = id` as ring
   homomorphisms, so `twistPushTransition_id` gives `T(id) = 𝟙`. Here `χ := GradedRingHom.id 𝒜`, whose irrelevant-ideal
   condition is given by `simp`, and `Proj.map id ≫ ι = ι` is Mathlib's `Proj.map_id`.
2. Take `Y := Proj 𝒜`, `ι_A := 𝟙`, `ι_B := Proj.map f` (so `Proj.map g ≫ Proj.map f = Proj.map (g ∘ f) = 𝟙`, by
   Mathlib's `Proj.map_comp` / `Proj.map_id` and `proj_map_congr`). By definition
   `T(f) = (𝟙)_*(θ_f) ≫ pushforwardComp.hom ≫ pushforwardCongr.hom`, and the last two factors are components of
   isomorphisms, so `(𝟙)_*(θ_f)` is an isomorphism (`IsIso.of_isIso_comp_right`); then `pushforwardId : (𝟙)_* ≅ 𝟭` and
   `NatIso.isIso_map_iff` give that `θ_f` is an isomorphism.
3. Substitute `ofVeronese` / `toVeronese` and `ofVeronese_comp_toVeronese` / `toVeronese_comp_ofVeronese`.

Edge cases: for `Proj 𝒜 = ∅` all morphisms are identities and the statement is trivial; for `f = id`, `θ_f` is the inverse
component of `pushforwardId`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Mutually inverse graded ring homomorphisms give mutually inverse transition maps: `T(f) ≫ T(g) = 𝟙` when `g ∘ f = id`. -/
theorem twistPushTransition_comp_eq_id (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = GradedRingHom.id 𝒜) (n : ℤ)
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y)
    (wf : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB)
    (wg : AlgebraicGeometry.Proj.map g hg ≫ ιB = ιA) :
    twistPushTransition f hf n ιA ιB wf ≫ twistPushTransition g hg n ιB ιA wg = 𝟙 _ := by
  have hid : HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (GradedRingHom.id 𝒜) := by simp
  have wid : AlgebraicGeometry.Proj.map (GradedRingHom.id 𝒜) hid ≫ ιA = ιA := by
    rw [AlgebraicGeometry.Proj.map_id, Category.id_comp]
  have hcomp : ((GradedRingHom.id 𝒜 : 𝒜 →+*ᵍ 𝒜) : A →+* A) =
      (g : B →+* A).comp (f : A →+* B) := by
    rw [← hgf]; rfl
  rw [← twistPushTransition_comp f g (GradedRingHom.id 𝒜) hf hg hid n hcomp ιA ιB ιA wf wg wid]
  exact twistPushTransition_id _ hid n rfl ιA wid

/-- The transition map of a graded ring homomorphism with a graded inverse is an isomorphism (the inverse is the
transition map in the other direction). -/
theorem isIso_twistPushTransition_of_inverse (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = GradedRingHom.id 𝒜) (hfg : f.comp g = GradedRingHom.id ℬ) (n : ℤ)
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y)
    (wf : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB)
    (wg : AlgebraicGeometry.Proj.map g hg ≫ ιB = ιA) :
    IsIso (twistPushTransition f hf n ιA ιB wf) :=
  ⟨twistPushTransition g hg n ιB ιA wg,
    twistPushTransition_comp_eq_id f g hf hg hgf n ιA ιB wf wg,
    twistPushTransition_comp_eq_id g f hg hf hfg n ιB ιA wg wf⟩

/-- `Proj.map g ≫ Proj.map f = 𝟙` when `g ∘ f = id` (Mathlib's `Proj.map_comp` / `Proj.map_id`). -/
theorem map_comp_map_eq_id_of_comp_eq_id (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = GradedRingHom.id 𝒜) :
    AlgebraicGeometry.Proj.map g hg ≫ AlgebraicGeometry.Proj.map f hf = 𝟙 _ := by
  rw [← AlgebraicGeometry.Proj.map_comp,
    AlgebraicGeometry.Scheme.relativeProj.veroneseIso.proj_map_congr hgf _ (by simp)]
  exact AlgebraicGeometry.Proj.map_id

/-- **The `θ` of a graded ring isomorphism is an isomorphism**: if `f : 𝒜 →+*ᵍ ℬ` has a graded inverse `g`, then
`Proj.twistToPushforward f hf n : O_{Proj 𝒜}(n) ⟶ (Proj.map f)_* O_{Proj ℬ}(n)` is an isomorphism. -/
theorem isIso_twistToPushforward_of_inverse (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = GradedRingHom.id 𝒜) (hfg : f.comp g = GradedRingHom.id ℬ) (n : ℤ) :
    IsIso (AlgebraicGeometry.Proj.twistToPushforward f hf n) := by
  have hT : IsIso (twistPushTransition f hf n (𝟙 (AlgebraicGeometry.Proj 𝒜))
      (AlgebraicGeometry.Proj.map f hf) (Category.comp_id _)) :=
    isIso_twistPushTransition_of_inverse f g hf hg hgf hfg n (𝟙 _) (AlgebraicGeometry.Proj.map f hf)
      (Category.comp_id _) (map_comp_map_eq_id_of_comp_eq_id f g hf hg hgf)
  have h1 : IsIso ((AlgebraicGeometry.Scheme.Modules.pushforward (𝟙 (AlgebraicGeometry.Proj 𝒜))).map
      (AlgebraicGeometry.Proj.twistToPushforward f hf n)) := by
    unfold twistPushTransition at hT
    exact IsIso.of_isIso_comp_right _
      ((AlgebraicGeometry.Scheme.Modules.pushforwardComp (AlgebraicGeometry.Proj.map f hf)
          (𝟙 (AlgebraicGeometry.Proj 𝒜))).hom.app (AlgebraicGeometry.Proj.twist ℬ n) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (Category.comp_id
          (AlgebraicGeometry.Proj.map f hf))).hom.app (AlgebraicGeometry.Proj.twist ℬ n))
  exact (NatIso.isIso_map_iff (AlgebraicGeometry.Scheme.Modules.pushforwardId
    (AlgebraicGeometry.Proj 𝒜)) (AlgebraicGeometry.Proj.twistToPushforward f hf n)).mp h1

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.relativeProj.veroneseIso

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (hm : 0 < m)

/-- Step 3a: `θ_{ofVeronese} : O_{Proj A(U)^{(m)}}(n) ⟶ (Proj.map ofVeronese)_* O_{Proj A^{(m)}(U)}(n)` is an isomorphism
(the graded inverse of `ofVeronese` is `toVeronese`). -/
theorem isIso_twistToPushforward_ofVeronese (U : X.Opens) (n : ℤ) :
    IsIso (AlgebraicGeometry.Proj.twistToPushforward (ofVeronese S m hm U)
      (irrelevant_le_map_ofVeronese S m hm U) n) :=
  AlgebraicGeometry.Proj.isIso_twistToPushforward_of_inverse (ofVeronese S m hm U) (toVeronese S m hm U)
    (irrelevant_le_map_ofVeronese S m hm U) (irrelevant_le_map_toVeronese S m hm U)
    (toVeronese_comp_ofVeronese S m hm U) (ofVeronese_comp_toVeronese S m hm U) n

/-- Step 3a in isomorphism form: `(Proj.map ofVeronese)_* O_{Proj A^{(m)}(U)}(n) ≅ O_{Proj A(U)^{(m)}}(n)`. -/
def twistPushforwardOfVeroneseIso (U : X.Opens) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map (ofVeronese S m hm U)
        (irrelevant_le_map_ofVeronese S m hm U))).obj
        (AlgebraicGeometry.Proj.twist ((S.veronese m).sectionsGrading U) n) ≅
      AlgebraicGeometry.Proj.twist (veroneseGrading (S.sectionsGrading U) m) n :=
  haveI := isIso_twistToPushforward_ofVeronese S m hm U n
  (asIso (AlgebraicGeometry.Proj.twistToPushforward (ofVeronese S m hm U)
    (irrelevant_le_map_ofVeronese S m hm U) n)).symm

end AlgebraicGeometry.Scheme.relativeProj.veroneseIso

end
