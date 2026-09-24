import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentLocallyFinitelyPresented
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.StalkLinearMapSpreads
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentHomGraph
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentHomGraphCoherent

/-! # Extending a linear map of stalks to a morphism of coherent sheaves

**A linear map between stalks of coherent sheaves is realized by a morphism defined on a coherent
sheaf that agrees with the source at the point** (Stacks 01BN + Stacks 01Y8, combined and specialized to
what the dévissage needs).

`X` Noetherian, `G`, `F` coherent, `ξ ∈ X`, `f : G_ξ → F_ξ` an `O_{X,ξ}`-linear map. Then there are a
coherent `G'`, morphisms `ι : G' → G`, `ψ : G' → F` with
* `Supp G' ⊆ Supp G ∪ Supp F`,
* `ι_ξ : G'_ξ → G_ξ` bijective,
* `ψ_ξ = f ∘ ι_ξ`.

(No monomorphism condition on `ι` is required: the dévissage only uses the stalk at `ξ` and the
supports, and handles `ker ι` and `coker ι` separately. A proof that produces a subsheaf `G' ⊆ G`, as
Stacks 01Y8 does, of course also proves this statement.)

**Natural-language proof.**

*Step 1 (Stacks 01BN: a stalk map spreads to a neighbourhood).* Choose an affine open `U = Spec A ∋ ξ`,
`A = Γ(X, U)` (Noetherian, `X` is locally Noetherian), and put `N := Γ(G, U)`, `M := Γ(F, U)`: finite
`A`-modules (`G`, `F` are coherent: `finite_sections_of_isFiniteType`, Stacks 01PB), hence finitely
presented (`Module.finitePresentation_of_finite`). Let `𝔭 ⊂ A` be the prime of `ξ`. By quasi-coherence
the stalks are the localizations: `G_ξ = N_𝔭`, `F_ξ = M_𝔭` along the germ maps
(`isLocalizedModule_germ`, `CoherentFreeStalksLocallyFree`; `O_{X,ξ} = A_𝔭`,
`IsAffineOpen.isLocalization_stalk`). Since `N` is finitely presented,
`Hom_A(N, M)_𝔭 = Hom_{A_𝔭}(N_𝔭, M_𝔭)` (Stacks 01BN / 0583; Mathlib: localization of `Hom` out of a
finitely presented module, `Module.FinitePresentation` API), so there are `s ∉ 𝔭` and an `A`-linear
`φ₀ : N → M` with `f = φ₀ ⊗ 1 / s` on the stalks; replacing `U` by the basic open `D(s) ∋ ξ` (affine,
`Γ(G, D(s)) = N_s`, `Γ(F, D(s)) = M_s`, `isLocalizedModule_basicOpen`), the map `φ₀/s : N_s → M_s` is
`Γ(X, D(s))`-linear and defines, through `G|_{D(s)} ≅ Ñ_s`, `F|_{D(s)} ≅ M̃_s` (quasi-coherence,
`fromTildeΓ` is an isomorphism for quasi-coherent modules, Stacks 01I8, as used in
`Stacks01y1`), a morphism `φ : G|_V → F|_V` on `V := D(s)` whose stalk at `ξ` is
`f`. *Summary of step 1:* there are an open `V ∋ ξ` and `φ : G|_V → F|_V` with `φ_ξ = f`.

*Step 2 (extension to a coherent sheaf on `X`).* Two routes, both with a source:
(a) *Stacks 01Y8's own argument*: let `𝓘 ⊆ O_X` be a coherent ideal sheaf with `V(𝓘) = X ∖ V`
(exists on a Noetherian scheme); by Stacks 01Y8 there is `n` with `𝓘^n · G ⊆ G` a coherent subsheaf
equal to `G` on `V` such that `φ` extends to `ψ : 𝓘^n G → F`; take `G' := 𝓘^n G`, `ι` the inclusion.
This needs the product `𝓘^n · G` of an ideal sheaf with a module sheaf and its basic properties
(Stacks 01YB), which the library does not have.
(b) *Fiber product (elementary, needs only Stacks 01LC)*: let `j : V → X` be the open immersion,
`j_* j^* F` the pushforward of `F|_V`; it is quasi-coherent because `j` is quasi-compact and
quasi-separated (`X` Noetherian; Stacks 01LC,
`Scheme.Modules.isQuasicoherent_pushforward`). Let `α : G → j_* j^* F` be the adjoint of
`φ : j^* G → j^* F` (`pullbackPushforwardAdjunction`) and `β : F → j_* j^* F` the unit. Put
`G' := ker (α − β ∘ pr) : G ⊕ F → j_* j^* F`, i.e. `G' = G ×_{j_* j^* F} F`, the fiber product; `ι := pr₁`,
`ψ := pr₂`. `G'` is quasi-coherent (kernel of a map of quasi-coherent modules, Stacks 01IC,
`isQuasicoherent_kernel`; `G ⊕ F` is quasi-coherent, `isQuasicoherent_biproduct`) and a subsheaf of the
coherent `G ⊕ F`, hence coherent (Stacks 01Y1, `isCoherent_of_mono`; `G ⊕ F` coherent by
`isCoherent_pow`-style biproduct lemmas, `Stacks0ayt_FiniteTypeBiproduct`). `Supp G' ⊆ Supp (G ⊕ F) =
Supp G ∪ Supp F`. Stalks at `ξ ∈ V`: `(j_* j^* F)_ξ = F_ξ` (pushforward along an open immersion does
not change stalks at points of the open, Mathlib `stalkPushforward_iso_of_isInducing` /
`PullbackStalkOpenImmersion`), `α_ξ = φ_ξ = f`, `β_ξ = id`, so `G'_ξ = {(a, b) ∈ G_ξ ⊕ F_ξ | f a = b}`,
`ι_ξ : (a, b) ↦ a` is bijective (inverse `a ↦ (a, f a)`) and `ψ_ξ (a, b) = b = f (ι_ξ (a, b))`.
Concretely (avoiding a computation of the stalk of a kernel): *injectivity* of `ι_ξ`: if the germ of
`(s, t) ∈ G'(W)` at `ξ` has `s_ξ = 0`, then `s = 0` on a smaller `W' ∋ ξ`, hence `t|_{W' ∩ V} =
φ(s|_{W' ∩ V}) = 0` and, shrinking `W'` into `V`, `t = 0` on `W'`, so `(s, t)_ξ = 0`. *Surjectivity*:
a germ `a ∈ G_ξ` is the germ of some `s ∈ G(W)` with `ξ ∈ W ⊆ V`; then `(s, φ(s)) ∈ G'(W)` maps to
`a`. *Compatibility*: `ψ (s, φ(s)) = φ(s)` has germ `φ_ξ(s_ξ) = f(a)`.

**Edge cases.** `F = 0`: `f = 0`; `G' = G`, `ι = 𝟙`, `ψ = 0` works. `G = 0`: `G' = 0`. `ξ ∉ Supp G`:
`f = 0` and `G' = G`, `ψ = 0` works (so the lemma is trivial off `Supp G`; the content is at points of
`Supp G`). `X` empty: no `ξ`. The statement is invariant under replacing `f` by `f ∘ e` for an
automorphism `e` of `G_ξ`.

**Formalization.** Step 1 via Stacks 01CP, step 2 via the fibre product (b). Four helper modules:
* `CoherentLocallyFinitelyPresented`: coherent on locally Noetherian ⇒ locally finitely presented
  in the concrete form `IsLocalPresentation` (`exists_isLocalPresentation_of_isCoherent`; Stacks 01XZ,
  proved from `finite_sections_of_isFiniteType`, the Noetherian property of `A^n`, and the basic-open
  localization lemmas `exists_pow_smul_eq_map_basicOpen` / `exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero`).
* `StalkLinearMapSpreads`: step 1, `exists_localHom_of_stalk_linearMap`, from the surjectivity half of
  Stacks 01CP (`Stacks01cp`, `localHomStalkHom_surjective_of_isLocalPresentation`): an open `V ∋ ξ`
  and `φ ∈ localHomSubmodule G F V` with `f [W, a] = [W, φ_W a]`.
* `CoherentHomGraph`: `G' := ker ((α, -β) : G ⊕ F → j_* j^* F)` with `α` the adjoint of `φ`
  (Mathlib `restrictAdjunction`) and `β` the unit; `ι = pr₁`, `ψ = pr₂`; the stalk statements at `ξ`
  (`graphFst_stalk_bijective`, `graphSnd_stalk_eq`) by the elementwise argument above.
* `CoherentHomGraphCoherent`: `G'` coherent (Stacks 01LC `isQuasicoherent_pushforward`, 01IC
  `isQuasicoherent_kernel`, 01Y1 `isCoherent_of_mono`; `G ⊞ F` coherent via `⨁ pairFunction G F`) and
  `Supp G' ⊆ Supp G ∪ Supp F`.

Source: Stacks 01BN (modules-lemma-finite-presentation-stalk / "morphisms of finitely presented
modules extend from stalks"), Stacks 01Y8 (coherent-lemma-extend-morphism), Stacks 01LC, 01IC, 01Y1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 01BN + 01Y8: an `O_{X,ξ}`-linear map
`f : G_ξ → F_ξ` between stalks of coherent sheaves on a Noetherian scheme is `ψ_ξ ∘ ι_ξ⁻¹` for a
coherent `G'` with `Supp G' ⊆ Supp G ∪ Supp F`, `ι : G' → G` bijective on the stalk at `ξ` and
`ψ : G' → F`. See the module docstring for the proof. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_coherent_hom_of_stalk_linearMap
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    (G F : X.Modules) [G.IsCoherent] [F.IsCoherent] (ξ : X)
    (f : G.stalk ξ →ₗ[X.presheaf.stalk ξ] F.stalk ξ) :
    ∃ (G' : X.Modules) (ι : G' ⟶ G) (ψ : G' ⟶ F), G'.IsCoherent ∧
      G'.support ⊆ G.support ∪ F.support ∧
      Function.Bijective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map ι).hom ∧
      ∀ m : G'.stalk ξ, ((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map ψ).hom m =
        f (((AlgebraicGeometry.Scheme.Modules.stalkFunctor ξ).map ι).hom m) := by
  obtain ⟨U, hξU, n, m, s, r, hsr⟩ :=
    MiyaokaMori.StalkHomSpread.exists_isLocalPresentation_of_isCoherent G ξ
  obtain ⟨V, hξV, φ, hf⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_localHom_of_stalk_linearMap G F ξ f hξU hsr
  exact ⟨MiyaokaMori.StalkHomSpread.graph G F φ, MiyaokaMori.StalkHomSpread.graphFst G F φ,
    MiyaokaMori.StalkHomSpread.graphSnd G F φ, MiyaokaMori.StalkHomSpread.graph_isCoherent G F φ,
    MiyaokaMori.StalkHomSpread.graph_support_subset G F φ,
    MiyaokaMori.StalkHomSpread.graphFst_stalk_bijective G F φ ξ hξV f hf,
    fun e => MiyaokaMori.StalkHomSpread.graphSnd_stalk_eq G F φ ξ hξV f hf e⟩

end
