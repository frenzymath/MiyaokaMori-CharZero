import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModulesAssociatedPoints
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.DenominatorMapsKernelEq
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.Stacks02oz
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.Stacks02p0
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.DenominatorMapsAssembly
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.DenominatorMapsStalkSurjective

/-! # The denominator-ideal trick of Snapper's theorem, with a coherent denominator module

The denominator-ideal trick of Stacks 0BEM (fourth paragraph), Stacks 02OZ + 02P2, **with the
coherence of `IF` in the conclusion**. This strengthens
`AlgebraicGeometry.Scheme.Modules.exists_denominator_maps` by `IF.IsCoherent`; without
that conclusion the statement is unusable in 0BEM, since the additivity of `χ` (Stacks 08AA)
needs all three terms of the short exact sequences `0 → IF → F → Q → 0`, `0 → IF → F ⊗ L → Q' → 0` to be
coherent, and coherence of the cokernels is itself derived from that of `IF`
(`isQuasicoherent_kernel`, `isCoherent_of_epi`). The weaker `exists_denominator_maps` is a one-line
consequence of this theorem (drop `IF.IsCoherent`); the converse does not hold (a mono `IF ⟶ F` alone
does not make `IF` quasi-coherent, e.g. `j_! O_U ⊆ O_X`).

**Statement.** `X` locally Noetherian with no embedded points; `F` coherent with no embedded associated
points and `Supp F = X`; `L` invertible. Then there are a coherent `O_X`-module `IF` and injective maps
`a : IF → F`, `b : IF → F ⊗ L` whose cokernels are supported in a closed subset `T ⊆ X` with empty interior.

**Proof (Stacks 0BEM, 02OZ, 02P2, 02P0), as formalized.** `exists_denominator_maps_isCoherent` below
is assembled from:
1. `nonempty_regularMeromorphicSection_of_noEmbeddedPoints` (Stacks 02OZ (3) = 0EMI): `L` has a regular
   meromorphic section `s` (locally `num_i / den_i` on a cover `U_i`, `den_i` a non-zero-divisor and
   `num_i` regular on every stalk).
2. `RegularMeromorphicSection.exists_denominatorIdeal` (Stacks 02P0): the ideal of denominators
   `I = {f : f s ∈ L}` with `a : I ⟶ O_X` (inclusion), `b : I ⟶ L` (multiplication by `s`), `I`
   quasi-coherent, `a`, `b` mono, and a closed `T` with empty interior containing the supports of
   `coker a`, `coker b`; plus the local relation `den_i • b(h) = a(h) • num_i`.
3. The two maps `Φ = denomMulMap a F : I ⊗ F ⟶ F`, `h ⊗ t ↦ a(h)•t`, and
   `Ψ = denomSectionMap b F : I ⊗ F ⟶ F ⊗ L`, `h ⊗ t ↦ t ⊗ b(h)`, have the same kernel on every stalk
   (`stalkMap_denomMulMap_eq_zero_iff`, Stacks 02P2):
   `den • ε(Ψ_x z) = Φ_x z ⊗ num` and `den`, `num` act injectively on `F_x` (`F` has no embedded associated
   points and `Supp F = X`, so non-zero-divisors of `O_{X,x}` are `F_x`-regular, Stacks 02P2/00LD/0587).
4. Off `T`, `a_x` and `b_x` are surjective (`notMem_support_cokernel_iff`), hence so are `Φ_x` and `Ψ_x`.
5. `I ⊗ F` is quasi-coherent (Stacks 01CE, `isQuasicoherent_tensor`), so the generic assembly
   `exists_coherent_factor_of_stalkMap_eq_zero_iff` gives
   `IF := coimage Φ` — coherent by Stacks 01IC + 01Y1 — with monos `a' : IF ⟶ F`, `b' : IF ⟶ F ⊗ L` and
   cokernels supported in `T`. Together with `IsClosed T`, `interior T = ∅` from step 2 this is the statement.

**Edge cases.** `X = ∅`: everything is trivial (`T = ∅`). `L = O_X`, `s = 1`: `I = O_X`, `IF ≅ F`, `T = ∅`, both
maps are isomorphisms and the cokernels vanish.

**Hypotheses (none can be dropped).** Without "no embedded points of `X`" a regular meromorphic section
may not exist (Stacks 0EMI needs it); without `Supp F = X` (or without `Ass F ⊆` generic points) `b` need not be
injective: for `F = κ(z)` at a closed point `z` where `s` is regular and vanishes, `I_z = O_{X,z}`, so `IF_z = F_z`
and `b_z = (t ↦ t ⊗ s_z) = 0` on `F_z ≠ 0` (this `F` has no embedded associated points, so only `Supp F = X` fails).

The user `exists_snapper_of_full_support` (`SnapperFullSupportStep.lean`) discharges every hypothesis
from its own (after 02OM has moved `F` to `Z = Supp F`) and uses every conjunct of the conclusion
(`IF.IsCoherent` for the coherence of the cokernels, `IsClosed T ∧ interior T = ∅` for
`IsNowhereDense T`, the two support inclusions for `dim Supp Q, Q' ≤ e`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Denominator maps with coherent `IF`** (Stacks 0BEM proof, 4th paragraph; 02OZ + 02P2 + 02P0).
See the module docstring for the complete proof. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_denominator_maps_isCoherent
    {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (hX : X.HasNoEmbeddedPoints)
    (F : X.Modules) [F.IsCoherent] (hF : F.HasNoEmbeddedAssociatedPoints) (hsupp : F.support = Set.univ)
    (L : X.Modules) [L.IsLineBundle] :
    ∃ (IF : X.Modules) (a : IF ⟶ F) (b : IF ⟶ F.tensor L) (T : Set X),
      IF.IsCoherent ∧ CategoryTheory.Mono a ∧ CategoryTheory.Mono b ∧ IsClosed T ∧ interior T = ∅ ∧
      (CategoryTheory.Limits.cokernel a).support ⊆ T ∧ (CategoryTheory.Limits.cokernel b).support ⊆ T := by
  -- Step 1: a regular meromorphic section (Stacks 02OZ)
  obtain ⟨s⟩ :=
    AlgebraicGeometry.Scheme.Modules.nonempty_regularMeromorphicSection_of_noEmbeddedPoints hX L
  -- Step 2: its ideal of denominators (Stacks 02P0)
  obtain ⟨I, a, b, T, hIqc, hmono_a, hmono_b, hT, hTint, hcoka, hcokb, hclause, -⟩ :=
    s.exists_denominatorIdeal
  have hFqc : F.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  have hPqc : (AlgebraicGeometry.Scheme.Modules.tensor I F).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensor I F
  -- Steps 3-5: assemble
  obtain ⟨IF, a', b', hIF, hma, hmb, hsa, hsb⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_coherent_factor_of_stalkMap_eq_zero_iff
      (AlgebraicGeometry.Scheme.Modules.denomMulMap a F)
      (AlgebraicGeometry.Scheme.Modules.denomSectionMap b F)
      (fun x z => AlgebraicGeometry.Scheme.Modules.stalkMap_denomMulMap_eq_zero_iff F hF hsupp s a b
        hclause x z)
      T
      (fun x hx => AlgebraicGeometry.Scheme.Modules.stalkMap_denomMulMap_surjective_of_surjective a F x
        ((AlgebraicGeometry.Scheme.Modules.notMem_support_cokernel_iff a x).mp fun h => hx (hcoka h)))
      (fun x hx => AlgebraicGeometry.Scheme.Modules.stalkMap_denomSectionMap_surjective_of_surjective b F x
        ((AlgebraicGeometry.Scheme.Modules.notMem_support_cokernel_iff b x).mp fun h => hx (hcokb h)))
  exact ⟨IF, a', b', T, hIF, hma, hmb, hT, hTint, hsa, hsb⟩

end
