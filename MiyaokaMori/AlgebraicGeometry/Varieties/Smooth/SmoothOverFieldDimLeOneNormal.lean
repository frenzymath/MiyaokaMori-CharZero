import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.RegularLocalRing.EtaleOverPIDLocalizationDomain
import MiyaokaMori.RingTheory.Dimension.EtaleOverPolynomialKrullDim
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks033m
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension

/-! # Smooth schemes of dimension at most one over a field are normal

A scheme smooth over a field with topological dimension `≤ 1` is normal (every stalk is an
integrally closed domain, in fact a PID); if moreover it is Noetherian and connected, it is
integral. The proof does not use the general "smooth implies regular" (Stacks 00TT / 056S) and
"a regular local ring is a domain" (Stacks 00NP): in dimension one it is a direct computation.
Every point has a standard smooth chart `K → Γ(X,V)` of relative dimension `n`;
`dim Γ(X,V) ≤ dim X ≤ 1` forces `n ≤ 1` (`le_one_of_ringKrullDim_le_one`), so `Γ(X,V)` is étale
over the PID `K[X_1..X_n]`, and its localizations at primes are domains and PIDs
(`localization_isDomain_and_isPrincipalIdealRing`).

Sources: the one-dimensional case of Stacks 056S; Stacks 033M (Noetherian, normal and connected
implies integral).
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- For a scheme smooth over a field with topological dimension `≤ 1`, every stalk is a domain and a
principal ideal ring. -/
theorem Smooth.stalk_isDomain_and_isPrincipalIdealRing_of_dim_le_one [Smooth f]
    (hdim : topologicalKrullDim X ≤ 1) (z : X) :
    IsDomain (X.presheaf.stalk z) ∧ IsPrincipalIdealRing (X.presheaf.stalk z) := by
  obtain ⟨U, hU, V, hV, hz, e, hf⟩ := Smooth.exists_isStandardSmooth f z
  have hUtop : U = ⊤ := by
    apply le_antisymm le_top
    intro y _
    have hy : y = f z := Subsingleton.elim _ _
    rw [hy]
    exact e hz
  subst U
  let _ : Field Γ(Spec (CommRingCat.of k), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  have : Nonempty V := ⟨⟨z, hz⟩⟩
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE ⊤ V e).hom.IsStandardSmoothOfRelativeDimension n := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
    let _ := (f.appLE ⊤ V e).hom.toAlgebra
    exact ⟨_, ⟨_, _, _, ‹_›, P, rfl⟩⟩
  have hVdim : ringKrullDim Γ(X, V) ≤ 1 := by
    calc ringKrullDim Γ(X, V) = topologicalKrullDim (Spec Γ(X, V)) := by
          change ringKrullDim Γ(X, V) = topologicalKrullDim (PrimeSpectrum Γ(X, V))
          exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, V)).symm
      _ = topologicalKrullDim V :=
          (IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph).symm
      _ ≤ topologicalKrullDim X := topologicalKrullDim_subspace_le X (V : Set X)
      _ ≤ 1 := hdim
  have hn1 : n ≤ 1 := hn.le_one_of_ringKrullDim_le_one hVdim
  let p := hV.primeIdealOf ⟨z, hz⟩
  obtain ⟨hdom, hpid⟩ :=
    hn.localization_isDomain_and_isPrincipalIdealRing hn1 p.asIdeal
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hz⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk z) p.asIdeal := hV.isLocalization_stalk ⟨z, hz⟩
  let φ : Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk z :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (X.presheaf.stalk z)).toRingEquiv
  have hdom' : IsDomain (X.presheaf.stalk z) := φ.toMulEquiv.isDomain_iff.mp hdom
  exact ⟨hdom', IsPrincipalIdealRing.of_surjective φ.toRingHom φ.surjective⟩

/-- A scheme smooth over a field with topological dimension `≤ 1` is normal. -/
theorem Smooth.isNormal_of_field_of_dim_le_one [Smooth f] (hdim : topologicalKrullDim X ≤ 1) :
    X.IsNormal where
  isDomain z := (Smooth.stalk_isDomain_and_isPrincipalIdealRing_of_dim_le_one f hdim z).1
  integrallyClosed z := by
    obtain ⟨_, _⟩ := Smooth.stalk_isDomain_and_isPrincipalIdealRing_of_dim_le_one f hdim z
    infer_instance

/-- A Noetherian connected scheme smooth over a field with topological dimension `≤ 1` is integral. -/
theorem Smooth.isIntegral_of_field_of_dim_le_one [Smooth f] [IsNoetherian X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X ≤ 1) : IsIntegral X := by
  have : X.IsNormal := Smooth.isNormal_of_field_of_dim_le_one f hdim
  exact isIntegral_of_isNormal_of_connected

end AlgebraicGeometry
