import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroJetCompatBridges

/-! # `restrictToThickening` as the section map of `thickIso`

Helper module for the compatibility of the morphism near the zero jet (used by
`MiyaokaMori.Paper.S3PositiveLine.MorphismNearZeroJetCompat`).

Content: the restriction of a global section of `π^*N` to the jet neighbourhood
(`restrictToThickening`, an instance of `AlgebraicGeometry.Scheme.Modules.restrictSectionAlong`) is the
section map of the isomorphism `thickIso i π p hp N : i^*π^*N ≅ p^*N` of `MorphismNearZeroJetCompatBridges`
applied to `i^*P`. In the paper this is the step in the proof of Theorem 4.2 where `Φ₀`
restricted to the jet neighbourhood is the projection of the jet.

Why a separate module, and why the statements are shaped this way (see also the notes in
`MorphismNearZeroJetCompatBridges`):
* Mathematically both statements are definitional unfoldings. The obstruction is the **kernel**, not
  the elaborator: `restrictSectionAlong` (a regular definition) and the section-level right-hand side
  (head `DFunLike.coe`, a projection, i.e. an abbreviation) are compared by the kernel's lazy delta
  reduction, which unfolds the *abbreviation* side first; on the concrete modules of the main theorem
  this evaluates the linear map down to `eqToHom` and then tries the K-rule
  `(pullback (i ≫ π)).obj N ≡ (pullback p).obj N`, which does not terminate in practice. On
  *variables* (`restrictSectionAlong_eq_thickIso_apply`) the same reduction gets stuck at once and
  the `rfl` is cheap. This is why the first lemma is stated on variables only.
* Consequently every use on concrete modules must go through `rw` with this lemma in such a way that
  the instantiated pattern is *structurally* (not just definitionally) the goal's term; in particular
  the implicit scheme arguments of `thickIso` and of `sectionPullbackAlong` must be spelled
  identically (`(totalSpace L.toModules).left` is spelled with `rho.source.toVariety.carrier` when
  elaborated on its own, but with `rho.source.toScheme` when inferred from the type of
  `(jetNeighborhood.toTotalSpace L κ).left`; pin `Z` explicitly). Then the remaining goal
  `restrictSectionAlong … = restrictToThickening …` has two regular heads and closes by `rfl`
  (argument-wise comparison, proof irrelevance for the abstracted proofs of the definition body).
* `restrictToThickening_eq_thickIso_apply` is the generic (curve-level) form in the spelling that
  comes from the type of `(jetNeighborhood.toTotalSpace L κ).left`; it is provided for reference and
  for users whose goals have that spelling (do not `rw` with it into a goal spelled with
  `(totalSpace L.toModules).left` pinned: the closing `rfl` would then be a kernel timeout). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open MorphismNearZeroJetCompat
noncomputable section

namespace MorphismNearZeroJetCompat

/-- On variables: `restrictSectionAlong i π N (congrArg _ hp) x` is `thickIso i π p hp N` applied to
`i^*x` (both are `((pullbackComp i π).app N).hom ≫ eqToHom _` applied to `i^*x`; `rfl`). -/
theorem restrictSectionAlong_eq_thickIso_apply {X Z W : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ Z)
    (π : Z ⟶ W) (p : X ⟶ W) (hp : i ≫ π = p) (N : W.Modules)
    (x : (((AlgebraicGeometry.Scheme.Modules.pullback π).obj N).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.restrictSectionAlong i π (g' := p) N
      (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj N) hp) x =
      ((thickIso i π p hp N).hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong i x) :=
  rfl

end MorphismNearZeroJetCompat

/-- `restrictToThickening L M κ P` is `thickIso i π p hp M.toModules` applied to `i^*P`, where
`i : C̃_(κ)(L) ↪ Tot(L)`, `π : Tot(L) → C̃`, `p = jetNeighborhood.proj L κ`, `hp : i ≫ π = p`
(the definition of `restrictToThickening`). Proof: unfold
`restrictToThickening` to `restrictSectionAlong` (`change`; both heads are regular definitions, so
this is cheap for the kernel) and apply `restrictSectionAlong_eq_thickIso_apply`. See the module
docstring for the spelling of the implicit arguments. -/
theorem restrictToThickening_eq_thickIso_apply {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    restrictToThickening L M κ P =
      (((thickIso (jetNeighborhood.toTotalSpace L κ).left
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (jetNeighborhood.proj L κ)
          (jetNeighborhood.toTotalSpace_proj L κ) M.toModules).hom.val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong (jetNeighborhood.toTotalSpace L κ).left P)) := by
  change AlgebraicGeometry.Scheme.Modules.restrictSectionAlong (jetNeighborhood.toTotalSpace L κ).left
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (g' := jetNeighborhood.proj L κ) M.toModules
    (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj M.toModules)
      (jetNeighborhood.toTotalSpace_proj L κ)) P = _
  rw [restrictSectionAlong_eq_thickIso_apply _ _ _ (jetNeighborhood.toTotalSpace_proj L κ)]

end
