import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffColimitQcFlasque
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffQcFlasqueAcyclic

/-! # A filtered colimit of injective sheaves is acyclic

A filtered colimit of injective abelian sheaves on a compact, quasi-separated space with a basis of
quasi-compact opens has vanishing higher cohomology: `H^{q+1}(X, colim_j I_j) = 0`.

This is the Čech step (third and fourth paragraphs of the proof) of Stacks 01FF
(cohomology-lemma-quasi-separated-cohomology-colimit). It is proved here **without Čech cohomology**, by Kempf's
argument (Kempf, "Some elementary proofs of basic theorems in the cohomology of quasi-coherent sheaves", Rocky
Mountain J. Math. 10 (1980), §2): the colimit is *qc-flasque* (`TopCat.Sheaf.IsQcFlasque`: restriction maps
between quasi-compact opens are surjective; `Stacks01ffColimitQcFlasque.lean`), and qc-flasque sheaves
on such a space are acyclic (`Stacks01ffQcFlasqueAcyclic.lean`, the Stacks 09SY / Hartshorne III.2.5
induction with "flasque" replaced by "qc-flasque"). Used in the inductive step of Stacks 01FF. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

/-- **Stacks 01FF, Čech step (Kempf's Čech-free proof).** Let `X` be compact and quasi-separated with a basis
`hB` of quasi-compact opens, `J` small filtered, and `I : J ⥤ Sh(X, Ab)` with every `I.obj j` injective. Then
`H^{q+1}(X, colim I) = 0` for all `q`.

**Proof.** Each `I_j` is flasque (Stacks 09SX, `TopCat.Sheaf.isFlasque_of_injective`). Hence `colim I` is
qc-flasque (`TopCat.Sheaf.isQcFlasque_colimit_of_isFlasque`: a section of `colim I` over a quasi-compact open
`U` comes from some `I_j(U)` by `sections_colimit_bijective_of_isCompact`, extends to `I_j(V)` for
`U ≤ V` since `I_j` is flasque, and maps to an extension in `(colim I)(V)`). Qc-flasque sheaves on a compact
quasi-separated space with a basis of quasi-compact opens have `H^{n+1} = 0`
(`TopCat.Sheaf.H_succ_subsingleton_of_isQcFlasque`): embed `F ↪ I'` injective with quotient `Q`; then
`Γ(X, I') → Γ(X, Q)` is onto (Kempf's gluing lemma over a finite cover of `X` by quasi-compact opens,
`TopCat.Sheaf.IsQcFlasque.surjective_app_of_shortExact`), which kills `H^1(F)` via the long exact sequence,
and `Q` is again qc-flasque (`TopCat.Sheaf.IsQcFlasque.of_shortExact`), so `H^{n+2}(F) ≅ H^{n+1}(Q) = 0` by
induction. -/
theorem TopCat.Sheaf.H_colimit_subsingleton_of_injective {X : TopCat.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    (hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    {J : Type u} [CategoryTheory.SmallCategory J] [CategoryTheory.IsFiltered J]
    (I : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hI : ∀ j, CategoryTheory.Injective (I.obj j)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H (CategoryTheory.Limits.colimit I) (q + 1)) := by
  have hflasque : ∀ j, TopCat.Sheaf.IsFlasque (I.obj j) := fun j =>
    haveI := hI j
    TopCat.Sheaf.isFlasque_of_injective (I.obj j)
  exact TopCat.Sheaf.H_succ_subsingleton_of_isQcFlasque hB q (CategoryTheory.Limits.colimit I)
    (TopCat.Sheaf.isQcFlasque_colimit_of_isFlasque hB I hflasque)

end
