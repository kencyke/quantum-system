# QuantumSystem

A Lean 4 formalization of quantum systems from an operator-algebraic perspective.

## Highlights

Notable results formalized in this repository include:

- **Gelfand–Naimark theorem** — every (possibly non-unital) C\*-algebra embeds
  isometrically as a \*-subalgebra of bounded operators on a Hilbert space,
  realized as a direct sum of GNS representations.
- **GNS construction** — for any state ω on a C\*-algebra, the associated
  cyclic representation (π_ω, H_ω, Ω_ω) with ω(a) = ⟨Ω_ω, π_ω(a) Ω_ω⟩.
- **Von Neumann bicommutant theorem (unital case / hard half)** — for any unital
  \*-subalgebra A of bounded operators on a complex Hilbert space,
  WOT-closedness (or SOT-closedness) implies A = A″.
- **Von Neumann entropy** — S(ρ) = −Tr(ρ log ρ) for finite-dimensional
  density matrices, together with non-negativity, the dimension bound
  S(ρ) ≤ log(dim), and concavity in ρ.
- **Umegaki relative entropy for finite-dimensional density matrices** —
  D(ρ‖σ) = Tr ρ (log ρ − log σ), defined on `EReal` so that
  supp(ρ) ⊄ supp(σ) is admitted as +∞.
- **Strong subadditivity of the von Neumann entropy** — for density matrices on a
  tripartite finite-dimensional tensor product ℋ_A ⊗ ℋ_B ⊗ ℋ_C,
  S(ρ_AB) + S(ρ_BC) ≥ S(ρ_ABC) + S(ρ_B). The current statement is
  *region-explicit*: the regions are concrete `Finset`s on a fixed `LocalNet`
  together with a common-region split (`ΛAB \ ΛA = ΛB`, `ΛABC \ ΛA = ΛBC`).
  An abstract formulation over a generic local net of algebras is not yet
  provided (**TODO**).
- **Lieb concavity for positive semidefinite matrices** — joint concavity of (A, B) ↦ Tr(Aᵖ K† B^(1−p) K)
  for 0 ≤ p ≤ 1, via Effros' matrix-convex argument.

