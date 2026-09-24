import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambda
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.RestrictToLambdaBundleFamilyTransition_PullbackTransition

/-! # Restricting a glued bundle family to a fibre of the deformation

Pullback along `sectionAt t : C → C × A¹` commutes with gluing: if `𝒱 = bundleFamilyOfCocycle U hU G hG`
carries block isomorphisms `e_α : 𝒱|_{W_α} ≅ O^r` (`W_α = toBase⁻¹ U_α`) compatible with the transitions
`freeTransition (W α) (W α') (G α' α)`, then `restrictToLambda 𝒱 t = (sectionAt t)^* 𝒱` carries block
isomorphisms `ε_α : (restrictToLambda 𝒱 t)|_{U_α} ≅ O^r` compatible with
`freeTransition (U α) (U α') (G α' α (t))`, where `G(t)` is `G` evaluated termwise at `λ = t` (`evalAt`).

Route: no pseudofunctor coherence; everything is computed at the level of **sections**:
* `…_PullbackSections`: the action of the base change isomorphism `baseChangeIso` of an open immersion
  square and of `pullbackObjFreeIso` on pulled-back sections `pullbackSectionsOn`; the inverse of the
  pulled-back block isomorphism `baseChangeFreeIso := bc ≪≫ s_α^*(e_α) ≪≫ pullbackObjFreeIso` sends `e_i`
  to the pulled-back frame section `s^*(e_α⁻¹ e_i)`.
* `…_FreeTransitionSections`: `IsTransitionCompatible … (freeTransition g) M e α α'` ⟺ the transition
  relation of the frame sections `e_α'(σ^α_i|_{k''P}) = Σ_j (swap g)_{ji}|_P • e_j`
  (`isTransitionCompatible_freeTransition_iff`).
* `…_PullbackTransition`: turn `he` into a relation between sections by the above equivalence, pull it
  back (semilinearly: coefficients go through `s^♯ = evalAt`), and turn it back into
  `IsTransitionCompatible`; the coefficients are compared by `coeff_identity` (both sides reduce to one
  `s.appLE`).
The general form `pullback_transition_exists` (`…_PullbackTransition`) holds for any `s : X → Y`,
`π : Y → X` with `s ≫ π = 𝟙`, independently of `C` and `A¹`; this module only specializes to `X = C`,
`Y = A¹_C`, `s = sectionAt t`, `π = toBase`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Pullback commutes with gluing: `restrictToLambda 𝒱 t` is trivial on `U_α`, with transition
matrices the values of `G_{α'α}` at `λ = t`.

Standard fact (pullback preserves local trivializations and transition functions; cf. Hartshorne II
Ex. 5.18).

Proof: `AlgebraicGeometry.Scheme.Modules.pullback_transition_exists` with `X = C`, `Y = A¹_C`,
`s = sectionAt t`, `π = toBase` (`s ≫ π = 𝟙` is `AffineSpace.homOfVector_over`), `M = 𝒱`,
`g α α' = G α' α`; `restrictToLambda 𝒱 t` is by definition `(pullback s).obj 𝒱`, `evalAt t W` is by
definition `s.appLE (π⁻¹W) W`, and `bundleFamilyOfCocycle.dataF` is by definition a free sheaf.

Edge cases: `ι` empty (the conclusion is trivial); `r = 0` (the free sheaf is the zero sheaf, all
morphisms are unique); `U_α = ⊥` (the restricted sheaf is zero). `t` is arbitrary (`k` any field, not
necessarily algebraically closed). -/
theorem restrictToLambda_bundleFamilyOfCocycle_transition {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens) (hU : ⨆ α, U α = ⊤)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G)
    (t : k)
    (e : ∀ α, (bundleFamilyOfCocycle U hU G hG).restrict
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α).ι ≅
      bundleFamilyOfCocycle.dataF (r := r) U α)
    (he : ∀ α α', AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α)
      (bundleFamilyOfCocycle.dataF (r := r) U)
      (fun α α' => AlgebraicGeometry.Scheme.Modules.freeTransition
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α)
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α') (G α' α))
      (bundleFamilyOfCocycle U hU G hG) e α α') :
    ∃ ε : ∀ α, (SheafOfModules.restrictToLambda (bundleFamilyOfCocycle U hU G hG) t).restrict (U α).ι ≅
        SheafOfModules.free (R := (U α).toScheme.ringCatSheaf) (ULift.{u} (Fin r)),
      ∀ α α', AlgebraicGeometry.Scheme.Modules.IsTransitionCompatible U
        (fun α => SheafOfModules.free (R := (U α).toScheme.ringCatSheaf) (ULift.{u} (Fin r)))
        (fun α α' => AlgebraicGeometry.Scheme.Modules.freeTransition (U α) (U α')
          ((G α' α).map (AlgebraicGeometry.Scheme.affineLineOver.evalAt C.toScheme t (U α' ⊓ U α))))
        (SheafOfModules.restrictToLambda (bundleFamilyOfCocycle U hU G hG) t) ε α α' :=
  AlgebraicGeometry.Scheme.Modules.pullback_transition_exists
    (AlgebraicGeometry.Scheme.affineLineOver.sectionAt (k := k) C.toScheme t)
    (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme)
    (AlgebraicGeometry.AffineSpace.homOfVector_over _ _) U (bundleFamilyOfCocycle U hU G hG)
    (fun α α' => G α' α) e he

end
