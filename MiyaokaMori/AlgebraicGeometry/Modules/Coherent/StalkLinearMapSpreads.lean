import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.Stacks01cp

/-! # A linear map of stalks spreads to a neighbourhood

**Stacks 01CP (surjectivity part), specialised.** `G`, `F` modules on a scheme `X`, `ξ ∈ X`, `G` with a
local presentation `(s, r)` on an open `U ∋ ξ` (`IsLocalPresentation`, `FinitePresentationLocalData.lean`),
`f : G_ξ → F_ξ` an `O_{X,ξ}`-linear map. Then there are an open `V ∋ ξ` and
`φ ∈ Hom_{O_V}(G|_V, F|_V) = localHomSubmodule G F V` whose stalk at `ξ` is `f`, in the elementwise form
`f [W, a] = [W, φ_W a]` for every `W ∈ Over V` containing `ξ` and every `a ∈ G(W)`.

Proof (assembly of `Stacks01cp.lean`): the canonical map `c = localHomStalkHom G F ξ` from the stalk of the
internal-Hom presheaf to `Hom(G_ξ, F_ξ)` is surjective because `G` is finitely presented near `ξ`
(`localHomStalkHom_surjective_of_isLocalPresentation`), so `f = c(h)` for some germ `h`; `h = [V, φ]` for
some open `V ∋ ξ` and `φ ∈ localHomSubmodule G F V` (`TopCat.Presheaf.exists_germ_eq`); the germ formula
`localHomStalkHom_germ_germ` gives `c([V, φ])([W, a]) = [W, φ_W a]`.

Source: Stacks 01CP (`modules-lemma-stalk-internal-hom`), used in Stacks 01BN / 01Y8.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **Step 1 of `exists_coherent_hom_of_stalk_linearMap`** (Stacks 01CP, surjectivity): an
`O_{X,ξ}`-linear map `f : G_ξ → F_ξ`, with `G` locally presented on `U ∋ ξ`, is the stalk of a
morphism `φ : G|_V → F|_V` on some open `V ∋ ξ`, i.e. `f [W, a] = [W, φ_W a]` for all `W ∈ Over V`
with `ξ ∈ W` and all `a ∈ G(W)`. -/
theorem exists_localHom_of_stalk_linearMap (G F : X.Modules) (ξ : X)
    (f : G.stalk ξ →ₗ[X.presheaf.stalk ξ] F.stalk ξ)
    {U : X.Opens} (hξU : ξ ∈ U) {n m : ℕ} {s : Fin n → Γ(G, U)} {r : Fin m → Fin n → Γ(X, U)}
    (hsr : AlgebraicGeometry.Scheme.Modules.IsLocalPresentation G U s r) :
    ∃ (V : X.Opens) (_ : ξ ∈ V) (φ : AlgebraicGeometry.Scheme.Modules.localHomSubmodule G F V),
      ∀ (W : CategoryTheory.Over V) (hξW : ξ ∈ W.left) (a : Γ(G, W.left)),
        f (G.presheaf.germ W.left ξ hξW a) = F.presheaf.germ W.left ξ hξW (φ.1 W a) := by
  obtain ⟨h, hh⟩ := AlgebraicGeometry.Scheme.Modules.localHomStalkHom_surjective_of_isLocalPresentation
    G F ξ (AlgebraicGeometry.Scheme.Modules.localHomStalkHom G F ξ)
    (AlgebraicGeometry.Scheme.Modules.localHomStalkHom_germ_germ G F ξ) hξU hsr f
  obtain ⟨V, hξV, φ, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf G F).presheaf h
  refine ⟨V, hξV, φ, fun W hξW a => ?_⟩
  rw [← hh]
  exact AlgebraicGeometry.Scheme.Modules.localHomStalkHom_germ_germ G F ξ V hξV φ W hξW a

end AlgebraicGeometry.Scheme.Modules

end
