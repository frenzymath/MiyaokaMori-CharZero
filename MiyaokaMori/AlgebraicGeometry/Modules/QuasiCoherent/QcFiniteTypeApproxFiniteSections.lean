import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcApproxSingleSection
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesQuasicoherentClosure
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree

/-! # Finite type approximation of finitely many sections of a quasi-coherent module

Finite-type approximation of a quasi-coherent module on a quasi-compact quasi-separated scheme
(Stacks, Properties of Schemes, §"Extending quasi-coherent sheaves", tags 01PD / 01PE; Görtz–Wedhorn,
Algebraic Geometry I, Thm. 10.47 and Cor. 10.50): finitely many sections `s i ∈ F(V i)` over affine opens
`V i` all come from one finite type quasi-coherent module `E` with a morphism `E ⟶ F`.

Used in Stacks 07RM (third and fourth paragraphs of the proof: "write `F = colim E_i` ... choose `i` such
that all `s_{j,t}` come from `E_i(V_j)`"). The proof is spread over the support modules `QcApproxGoodOn`,
`QcApproxSpanAffine`, `QcApproxSpanSubpresheaf`, `QcApproxExtendAffine`, `QcApproxGlue`,
`QcApproxSingleSection` in this directory.

**Route actually formalized** (Stacks 01PC–01PE, in "sub-presheaf" form, without pushforwards or kernels).
For one section `s ∈ F(V)`: a sub-presheaf `G ⊆ F` is *good on an open `U`* (`QcApprox.GoodOn`) if on the
opens inside `U` its membership is local, it has the localization property on affines (quasi-coherence), it
is saturated in `F` on affines, and it is spanned by finitely many sections near every point (finite type).
* `spanSub F V (fun _ => s)` (sections locally a multiple of `s`) is good on the affine `V`
  (`goodOn_spanSub`; uses "locally in a span ⇒ in the span" on affines, `mem_span_of_locally`).
* Stacks 01PC (`GoodOn.exists_spanSub_agree`): `G` good on a quasi-compact `U`, `W` affine ⇒ finitely many
  `e i ∈ F(W)` with `spanSub F W e = G` on opens `≤ U ⊓ W` (cover `U ⊓ W` by basic opens `D(g)` of `W` on
  which `G` is finitely generated; lift generators to `W` up to powers of `g`, using saturation).
* Gluing (`GoodOn.glue`): two good sub-presheaves agreeing on `U ⊓ W` glue to one good on `U ⊔ W`.
* Induction over a finite affine cover of `S` gives `G` good on `⊤` with `s ∈ G(V)`; `toModules G` is the
  required `E` (quasi-coherent by `isQuasicoherent_of_affine_localizing`, finite type by
  `isFiniteType_of_finite_affine_sections`).
Finitely many sections: take the biproduct `⨁ E i` of the modules for each `s i` and `biproduct.desc`
(the statement does not require `φ` to be a monomorphism, so no sum of submodules is needed).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Finite type approximation of finitely many local sections** (Stacks 01PD–01PE, Görtz–Wedhorn
Thm. 10.47 / Cor. 10.50, in the form used by Stacks 07RM).

Let `S` be a quasi-compact quasi-separated scheme, `F` a quasi-coherent `O_S`-module, `V 0, …, V (n-1)`
affine opens of `S` and `s i ∈ F(V i)`. Then there are a **finite type** quasi-coherent module `E`, a
morphism `φ : E ⟶ F`, and sections `e i ∈ E(V i)` with `φ(e i) = s i` for every `i`.

The statement does not require `φ` to be a monomorphism (Stacks produces a submodule `E ⊆ F`; the weaker
form is all that Stacks 07RM uses). Proof: for each `i`, `exists_isFiniteType_hom_of_affine_section` gives
`E i ⊆ F` finite type quasi-coherent with `s i ∈ E i (V i)`; take `E := ⨁ E i` (quasi-coherent:
`isQuasicoherent_biproduct_of_fintype`; finite type: `biproduct_isFiniteType`), `φ := biproduct.desc`, and
`e i := biproduct.ι E i (s i)`; `biproduct.ι_desc` gives `φ (e i) = s i`. See the module docstring for
the route. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_isFiniteType_hom_of_finite_affine_sections
    {S : AlgebraicGeometry.Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (F : S.Modules) [F.IsQuasicoherent] {n : ℕ} (V : Fin n → S.affineOpens)
    (s : ∀ i, Γ(F, (V i).1)) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteType) (φ : E ⟶ F)
      (e : ∀ i, Γ(E, (V i).1)),
      ∀ i, (φ.val.app (Opposite.op (V i).1)).hom (e i) = s i := by
  choose E hqc hft φ e he using fun i =>
    AlgebraicGeometry.Scheme.Modules.QcApprox.exists_isFiniteType_hom_of_affine_section F (V i).2 (s i)
  have : ∀ i, (E i).IsFiniteType := hft
  refine ⟨⨁ E, AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct_of_fintype E hqc, inferInstance,
    biproduct.desc φ, fun i => ((biproduct.ι E i).val.app (Opposite.op (V i).1)).hom (e i), fun i => ?_⟩
  have h1 : biproduct.ι E i ≫ biproduct.desc φ = φ i := biproduct.ι_desc φ i
  rw [← he i, ← h1]
  rfl

end
