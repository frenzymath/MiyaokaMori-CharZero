import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenterAffineLeaf

/-! # The blowup is an isomorphism over the complement of the centre

Stacks 02OS(1): the blowup `b : Bl_I X → X` is an isomorphism over the open `X ∖ V(I) = I.support.compl`
(the locus where `I` is the unit ideal).

Source: Stacks 02OS(1) ("the first statement just means that X' = X if Z = ∅"), via Stacks 01MI in its
abstract form (`Proj.toSpecZero 𝒜` is an isomorphism as soon as some `t ∈ 𝒜 1` multiplies `𝒜 n`
bijectively onto `𝒜 (n+1)`; `Proj.isIso_toSpecZero_of_degreeOne_generator`).
This is the input of the uniqueness half of Stacks 0806 (`BlowupLiftUnique`); it is not derived from the
universal property `IsBlowup` (which is proved from it).

Proof: by the affine-local statement `isIso_reesAlgebra_projToOpen_of_ideal_eq_top`
(`BlowupIsoAwayFromCenterAffineLeaf`), on every affine open `U` with `I(U) = ⊤` the chart structure map
`projToOpen U : Proj S(U) → U` of the relative Proj of the Rees algebra is an isomorphism; the two gluing
lemmas below (chart ↔ restriction, Zariski locality of `IsIso` on the target) are the same as in
`BlowupIsoAwayFromCenter`, repeated here as `private` declarations because that module imports this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Chart ↔ restriction: the chart `Proj S(U) → U` of the relative Proj (Stacks 01NQ,
`projChart_isPullback`) is the base change of the structure map along `U ↪ X`, as is
`relativeProj.hom ∣_ U` (`isPullback_morphismRestrict`); so the two are isomorphic over `U` and one is
an isomorphism iff the other is. -/
private theorem isIso_relativeProj_hom_restrict_of_isIso_projToOpen {X : Scheme.{u}}
    (S : X.GradedAffineAlgebra) (U : X.AffineZariskiSite) [IsIso (S.projToOpen U)] :
    IsIso (S.relativeProj.hom ∣_ U.toOpens) := by
  have h₁ := S.projChart_isPullback U
  have h₂ := isPullback_morphismRestrict S.relativeProj.hom U.toOpens
  have he : (h₁.isoIsPullback _ _ h₂).inv ≫ S.projToOpen U = S.relativeProj.hom ∣_ U.toOpens :=
    h₁.isoIsPullback_inv_fst _ _ h₂
  rw [← he]
  infer_instance

/-- **Stacks 02OS(1), for an arbitrary open `U` disjoint from the support of `I`**: `b ∣_ U` is an
isomorphism. `IsIso` is Zariski-local on the target (`IsZariskiLocalAtTarget` for
`MorphismProperty.isomorphisms`), so it suffices to treat the affine opens `V` of `U`; the image
`U.ι ''ᵁ V` is an affine open of `X` inside `U`, hence disjoint from the support, hence `I(U.ι ''ᵁ V) = ⊤`
(`ideal_eq_top_of_disjoint_support`); the affine leaf `isIso_reesAlgebra_projToOpen_of_ideal_eq_top`
and the chart ↔ restriction lemma above give `IsIso (b ∣_ (U.ι ''ᵁ V))`, and
`morphismRestrictRestrict` identifies this with `(b ∣_ U) ∣_ V`. -/
private theorem isIso_blowup_hom_restrict_of_disjoint_support' {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.Opens) (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso ((Scheme.blowup I).hom ∣_ U) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun V : U.toScheme.affineOpens => (V : U.toScheme.Opens)) (iSup_affineOpens_eq_top _) ?_
  intro V
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (Scheme.blowup I).hom U V.1), MorphismProperty.isomorphisms.iff]
  have hV : IsAffineOpen (U.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion U.ι
  have hle : U.ι ''ᵁ V.1 ≤ U :=
    (U.ι.image_le_opensRange V.1).trans (le_of_eq (Scheme.Opens.opensRange_ι U))
  have htop : I.ideal ⟨U.ι ''ᵁ V.1, hV⟩ = ⊤ :=
    I.ideal_eq_top_of_disjoint_support ⟨_, hV⟩ (hU.mono_left (fun _ h => hle h))
  have := I.isIso_reesAlgebra_projToOpen_of_ideal_eq_top ⟨U.ι ''ᵁ V.1, hV⟩ htop
  exact isIso_relativeProj_hom_restrict_of_isIso_projToOpen I.reesAlgebra.toGradedAffineAlgebra
    ⟨U.ι ''ᵁ V.1, hV⟩

end AlgebraicGeometry

/-- **Stacks 02OS(1)**: `b ∣_ W` is an isomorphism, `W := I.support.compl` (the open where `I = O_X`).

Proof. `W = X ∖ supp I` is disjoint from `supp I` (`disjoint_compl_left`; the underlying set of
`Closeds.compl` is the set complement by definition), so `isIso_blowup_hom_restrict_of_disjoint_support'`
above applies: `IsIso` is Zariski-local on the target, and on every affine open `V ⊆ W` of `X` one has
`I(V) = ⊤`, where the chart `Proj S(V) → V` of the Rees algebra `S = ⊕ Iⁿ` is `Proj Γ(V)[T] → Spec Γ(V)`,
an isomorphism by Stacks 01MI (`isIso_reesAlgebra_projToOpen_of_ideal_eq_top`).

Edge cases: `I = ⊥`: `W = ∅`, `b ∣_ ∅ : ∅ → ∅` is an isomorphism (both sides empty). `I = ⊤`: `W = X`
and the statement says `Bl_⊤ X ≅ X`, which is 01MI. `X = ∅`: trivial. -/
theorem AlgebraicGeometry.Scheme.blowup_isIso_morphismRestrict_support_compl
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) :
    CategoryTheory.IsIso ((AlgebraicGeometry.Scheme.blowup I).hom ∣_ I.support.compl) :=
  AlgebraicGeometry.isIso_blowup_hom_restrict_of_disjoint_support' I I.support.compl
    (show Disjoint ((I.support : Set X)ᶜ) (I.support : Set X) from disjoint_compl_left)

end
