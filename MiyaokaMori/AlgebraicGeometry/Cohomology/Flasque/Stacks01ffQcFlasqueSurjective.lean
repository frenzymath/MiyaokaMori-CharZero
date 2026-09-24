import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffQcFlasqueGlue

/-! # Surjectivity on sections over quasi-compact opens (Kempf's lemma)

Kempf's lemma (Kempf, "Some elementary proofs of basic theorems in the cohomology of quasi-coherent sheaves",
Rocky Mountain J. Math. 10 (1980), §2): on a quasi-separated space with a basis of quasi-compact opens, if
`0 → F → G → H → 0` is a short exact sequence of abelian sheaves with `F` qc-flasque, then `G(U) → H(U)` is
surjective for every quasi-compact open `U`. This is the qc-analogue of Hartshorne II Ex. 1.16(b) / Mathlib
`TopCat.Sheaf.IsFlasque.epi_of_shortExact`, with Zorn's lemma replaced by an induction over a finite cover.
Used in `Stacks01ffQcFlasqueQuotient.lean` and `Stacks01ffQcFlasqueAcyclic.lean`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- (Kempf 1980 §2.) Let `X` be quasi-separated with a basis `hB` of quasi-compact opens,
`0 → F → G → H → 0` short exact in `Sh(X, Ab)` with `F` qc-flasque, and `U` a quasi-compact open. Then
`G(U) → H(U)` is surjective.

**Proof.** Let `s ∈ H(U)`. Since `g` is an epimorphism of sheaves it is locally surjective
(`TopCat.Sheaf.isLocallySurjective_iff_epi`, `TopCat.Presheaf.isLocallySurjective_iff`): every `x ∈ U` has an
open `V ≤ U` containing `x` on which `s|_V` lifts to `G(V)`; shrink `V` to a basic quasi-compact open
`V_x ∋ x`, `V_x ≤ V` (`Opens.isBasis_iff_nbhd`) and restrict the lift. As `U` is quasi-compact, finitely many
`V_{x_1}, …, V_{x_n}` cover `U` (`IsCompact.elim_finite_subcover`). By induction on `k` (`Finset.induction_on`)
`s|_{W_k}` lifts to `G(W_k)` where `W_k := V_{x_1} ⊔ … ⊔ V_{x_k}` (`Finset.sup`), which is quasi-compact
(`Finset.isCompact_biUnion`): for `k = 0`, `W_0 = ∅` and `H(∅) = 0` (`TopCat.Sheaf.eq_of_locally_eq'` with the
empty cover), so `0` is a lift; the step `W_k → W_k ⊔ V_{x_{k+1}}` is
`TopCat.Sheaf.IsQcFlasque.exists_lift_sup`, which uses that `W_k ⊓ V_{x_{k+1}}` is quasi-compact
(`X` quasi-separated) and that `F` is qc-flasque. Finally `W_n = U`, and a lift of `s|_U = s` is what we want.
Edge cases: `U = ∅` (the finite subcover is empty and the base case applies); `n = 0` likewise. -/
theorem IsQcFlasque.surjective_app_of_shortExact [QuasiSeparatedSpace X]
    (hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    {S : CategoryTheory.ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (h₁ : TopCat.Sheaf.IsQcFlasque S.X₁) (U : TopologicalSpace.Opens X)
    (hU : IsCompact (U : Set X)) : Function.Surjective (S.g.hom.app (op U)) := by
  classical
  intro s
  -- local lifts of `s` on basic quasi-compact opens
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi S.g).2 hS.epi_g) U s
  have hpt : ∀ x : U, ∃ V : Opens X, IsCompact (V : Set X) ∧ (x : X) ∈ V ∧
      ∃ (e : V ≤ U) (a : S.X₂.obj.obj (op V)), S.g.hom.app (op V) a = S.X₃.obj.map (homOfLE e).op s := by
    intro x
    obtain ⟨V₀, hV₀U, ⟨a₀, ha₀⟩, hxV₀⟩ := hloc x.1 x.2
    obtain ⟨V, hVc, hxV, hVV₀⟩ := (Opens.isBasis_iff_nbhd.1 hB) hxV₀
    refine ⟨V, hVc, hxV, hVV₀.trans hV₀U, S.X₂.obj.map (homOfLE hVV₀).op a₀, ?_⟩
    rw [TopCat.Sheaf.app_res, ha₀]
    exact TopCat.Sheaf.res_res S.X₃ hVV₀ hV₀U s
  choose V hVc hxV e a ha using hpt
  -- finite subcover of the quasi-compact `U`
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U => (V x : Set X)) (fun x => (V x).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  -- induction over finite sets of indices: a lift exists over `t.sup V`
  have key : ∀ t : Finset U, ∃ c : S.X₂.obj.obj (op (t.sup V)),
      S.g.hom.app (op (t.sup V)) c = S.X₃.obj.map (homOfLE (Finset.sup_le fun x _ => e x)).op s := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨0, ?_⟩
      -- sections over `∅.sup V = ⊥` form a singleton (sheaf condition for the empty cover)
      refine TopCat.Sheaf.eq_of_locally_eq' S.X₃ (fun i : PEmpty.{u + 1} => (⊥ : Opens X)) _
        (fun i => i.elim) ?_ _ _ (fun i => i.elim)
      rw [Finset.sup_empty]
      exact bot_le
    | insert x t _ ih =>
      obtain ⟨c, hc⟩ := ih
      have hts : IsCompact ((t.sup V : Opens X) : Set X) := by
        rw [Opens.coe_finset_sup, Finset.sup_set_eq_biUnion]
        exact t.isCompact_biUnion (fun i _ => hVc i)
      have hsup : (insert x t).sup V = V x ⊔ t.sup V := Finset.sup_insert
      obtain ⟨c', hc'⟩ := TopCat.Sheaf.IsQcFlasque.exists_lift_sup hS h₁ (hVc x) hts (e x)
        (Finset.sup_le fun y _ => e y) s (a x) (ha x) c hc
      refine ⟨S.X₂.obj.map (homOfLE hsup.le).op c', ?_⟩
      rw [TopCat.Sheaf.app_res, hc', TopCat.Sheaf.res_res]
  obtain ⟨c, hc⟩ := key t
  have hUt : U ≤ t.sup V := fun y hy => by
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact Finset.le_sup (f := V) hi hyi
  refine ⟨S.X₂.obj.map (homOfLE hUt).op c, ?_⟩
  rw [TopCat.Sheaf.app_res, hc, TopCat.Sheaf.res_res]
  have hid : (homOfLE (hUt.trans (Finset.sup_le fun x _ => e x)) : U ⟶ U) = 𝟙 U := rfl
  rw [hid, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

end TopCat.Sheaf

end
