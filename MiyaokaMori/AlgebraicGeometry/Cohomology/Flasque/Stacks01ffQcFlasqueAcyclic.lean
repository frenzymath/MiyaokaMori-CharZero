import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffQcFlasqueQuotient
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks09sy

/-! # Qc-flasque sheaves are acyclic (Kempf)

Kempf's theorem (Kempf, "Some elementary proofs of basic theorems in the cohomology of quasi-coherent sheaves",
Rocky Mountain J. Math. 10 (1980), §2): on a compact quasi-separated space with a basis of quasi-compact opens,
a qc-flasque abelian sheaf has `H^{n+1}(X, F) = 0`. The proof is that of Hartshorne III.2.5 / Stacks 09SY
(`TopCat.Sheaf.H_succ_subsingleton_of_isFlasque`) with "flasque" replaced by "qc-flasque": the two
facts used about flasque sheaves there — `Γ(X, G) → Γ(X, H)` is onto and the quotient is again flasque — are
`IsQcFlasque.surjective_app_of_shortExact` (with `U = X`, quasi-compact) and `IsQcFlasque.of_shortExact`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- On a compact space the open `⊤` is quasi-compact. -/
theorem isCompact_coe_top [CompactSpace X] : IsCompact ((⊤ : TopologicalSpace.Opens X) : Set X) := by
  rw [Opens.coe_top]; exact isCompact_univ

/-- `H^1` step (Kempf 1980 §2; cf. `TopCat.Sheaf.H_one_subsingleton_of_shortExact_of_isFlasque`): in a short
exact sequence `0 → F → G → H → 0` of abelian sheaves on a compact quasi-separated space with a basis of
quasi-compact opens, if `F` is qc-flasque and `H^1(G) = 0` then `H^1(F) = 0`. By the long exact sequence
`H^0(G) → H^0(H) → H^1(F) → H^1(G) = 0` (`Abelian.Ext.covariant_sequence_exact₁`) every class in `H^1(F)` is
the image of a class in `H^0(H) = Γ(X, H)` (`Sheaf.H.equiv₀`), and `Γ(X, G) → Γ(X, H)` is surjective by
`IsQcFlasque.surjective_app_of_shortExact` with `U = ⊤` (quasi-compact since `X` is compact), so the
connecting map vanishes. -/
theorem H_one_subsingleton_of_shortExact_of_isQcFlasque [CompactSpace X] [QuasiSeparatedSpace X]
    (hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    {S : CategoryTheory.ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (h₁ : TopCat.Sheaf.IsQcFlasque S.X₁) [Subsingleton (CategoryTheory.Sheaf.H S.X₂ 1)] :
    Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ :=
    Abelian.Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) (zero_add 1)
  have hsurj : Function.Surjective (S.g.hom.app (op (⊤ : Opens X))) :=
    TopCat.Sheaf.IsQcFlasque.surjective_app_of_shortExact hB hS h₁ ⊤ isCompact_coe_top
  obtain ⟨y, hy⟩ := hsurj (CategoryTheory.Sheaf.H.equiv₀ S.X₃ Limits.isTerminalTop x₃)
  have h2 : CategoryTheory.Sheaf.H.map S.g 0
      ((CategoryTheory.Sheaf.H.equiv₀ S.X₂ Limits.isTerminalTop).symm y) = x₃ := by
    rw [CategoryTheory.Sheaf.H.equiv₀_symm_naturality, hy, AddEquiv.symm_apply_apply]
  rw [← hx₃, ← h2, CategoryTheory.Sheaf.H.map_apply, Abelian.Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Abelian.Ext.comp_zero]

/-- (Kempf 1980 §2; the qc-flasque version of Stacks 09SY / Hartshorne III.2.5.) Let `X` be compact
and quasi-separated with a basis of quasi-compact opens, and `F` a qc-flasque abelian sheaf. Then
`H^{n+1}(X, F) = 0` for all `n`.

**Proof** (induction on `n`, simultaneously for all qc-flasque `F`). Embed `F` into an injective `I`
(`Injective.under F`; `Sh(X, Ab)` has enough injectives) with quotient `Q := cokernel`, giving a short exact
sequence `0 → F → I → Q → 0` (`TopCat.Sheaf.cokernelSequence_injectiveι_shortExact`). `I` is flasque
(Stacks 09SX, `TopCat.Sheaf.isFlasque_of_injective`) and `H^{m+1}(I) = 0` for all `m` (Mathlib instance for
injective sheaves). `n = 0`: `H_one_subsingleton_of_shortExact_of_isQcFlasque`. `n + 1`: `Q` is qc-flasque by
`IsQcFlasque.of_shortExact`, so `H^{n+1}(Q) = 0` by induction, and the long exact sequence
`H^{n+1}(Q) → H^{n+2}(F) → H^{n+2}(I) = 0` (`CategoryTheory.Sheaf.subsingleton_H_X₁_of_shortExact`) gives
`H^{n+2}(F) = 0`. -/
theorem H_succ_subsingleton_of_isQcFlasque [CompactSpace X] [QuasiSeparatedSpace X]
    (hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)}) (n : ℕ) :
    ∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      TopCat.Sheaf.IsQcFlasque F → Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  induction n with
  | zero =>
    intro F hF
    have hS := TopCat.Sheaf.cokernelSequence_injectiveι_shortExact F
    have h2 : Subsingleton
        (CategoryTheory.Sheaf.H (ShortComplex.cokernelSequence (Injective.ι F)).X₂ (0 + 1)) :=
      inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H (Injective.under F) (0 + 1)))
    exact H_one_subsingleton_of_shortExact_of_isQcFlasque hB hS hF
  | succ n ih =>
    intro F hF
    have hS := TopCat.Sheaf.cokernelSequence_injectiveι_shortExact F
    have hI : TopCat.Sheaf.IsFlasque (ShortComplex.cokernelSequence (Injective.ι F)).X₂ :=
      TopCat.Sheaf.isFlasque_of_injective (Injective.under F)
    have hQ : TopCat.Sheaf.IsQcFlasque (ShortComplex.cokernelSequence (Injective.ι F)).X₃ :=
      TopCat.Sheaf.IsQcFlasque.of_shortExact hB hS hF
    have h3 : Subsingleton
        (CategoryTheory.Sheaf.H (ShortComplex.cokernelSequence (Injective.ι F)).X₃ (n + 1)) :=
      ih _ hQ
    have h2 : Subsingleton
        (CategoryTheory.Sheaf.H (ShortComplex.cokernelSequence (Injective.ι F)).X₂ (n + 1 + 1)) :=
      inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H (Injective.under F) (n + 1 + 1)))
    exact CategoryTheory.Sheaf.subsingleton_H_X₁_of_shortExact hS (n + 1) (n + 1 + 1) rfl

end TopCat.Sheaf

end
