---
name: paper-notation-refactor
description: Refactor Lean 4 code toward publication-style notation. Two modes. (A) Apply existing Mathlib notation — e.g. `inner ℂ x y` → `⟪x, y⟫_ℂ`, `Finset.sum Finset.univ f` → `∑ i, f i`, `norm x` → `‖x‖`, `Complex.I` → `I`, `Real.pi` → `π`, `ContinuousLinearMap.adjoint f` → `f†`. (B) Design brand-new `scoped notation` (and companion `Coe` instances) for domain concepts with standard textbook renderings but no Mathlib spelling — e.g. quantum relative entropy `D(ρ ‖ σ) = Tr (ρ (log ρ − log σ))`, GNS representation `π_ω`, cyclic vector `Ω_ω`, modular operator `Δ_ω`, KMS state `ω_β`, partial trace `Tr_B`. Invoke this skill whenever the user talks about "paper notation", "textbook style", "publication style", "make this look like the paper", "use `⟪·, ·⟫`", "rewrite inner product notation", "add notation for …", "introduce notation so the statement reads like Araki / Bratteli–Robinson / Nielsen–Chuang / Reed–Simon", or when editing a `.lean` file that contains long-form notation calls (`inner ℂ _ _`, `Finset.sum Finset.univ`, `ContinuousLinearMap.adjoint`) where a Unicode / mixfix form already exists in Mathlib. Also trigger when the user asks to introduce or design a new operator / relation symbol. Do NOT trigger for proof-structure or tactic rewrites (those go to `lean4:refactor` / `lean4:golf`), for removing unused hypotheses (that is `derivable-hypothesis-remover`'s job), or for renaming identifiers.
---

# paper-notation-refactor

Rewrite Lean 4 code so a human reading the file sees the same symbols a
physics / operator-algebra paper uses — `⟪x, y⟫_ℂ` instead of
`inner ℂ x y`, `D(ρ ‖ σ)` instead of `quantumRelativeEntropy ρ σ`, `∑ i, f i`
instead of `Finset.sum Finset.univ fun i => f i`.

## When to invoke

- The user says "paper style", "textbook style", "publication style",
  "make this look like the paper", "rewrite notation", "add notation for
  X".
- The user points at a `.lean` file and asks to "clean up" or "make it
  nicer" and that file has long-form `inner _ _`, `norm _`, `Finset.sum
  Finset.univ _`, or domain-specific long-form calls that have a
  textbook rendering.
- The user wants to introduce a new symbol (`D(ρ ‖ σ)`, `π_ω`, `Ω_ω`,
  `Δ_ω`, `Tr_B`) for an existing Lean definition.

## When NOT to invoke

- The user wants to restructure a proof, change tactics, extract a
  helper lemma, or improve a proof strategy. Use `lean4:refactor` or
  `lean4:golf`.
- The user wants to remove unused hypotheses or weaken typeclass
  assumptions. Use `derivable-hypothesis-remover` (sibling skill).
- The user wants to introduce a new mathematical *definition*. This
  skill only adds `notation`, `scoped notation`, `syntax` + `macro_rules`,
  and narrowly-scoped `Coe` instances — never fresh `def`s, `theorem`s,
  or `structure`s.

## Modes of operation

### Mode A — apply existing Mathlib notation

For each pattern below, the skill grep-scans the target file, confirms the
required scope, and substitutes. Each rewrite is followed by
`lean_diagnostic_messages` on the file; if red, the skill reverts that one
rewrite and continues.

| long form                                                | paper form      | scope to open                                 |
| -------------------------------------------------------- | --------------- | --------------------------------------------- |
| `inner ℂ x y`                                            | `⟪x, y⟫_ℂ`      | `open scoped InnerProductSpace`               |
| `inner ℝ x y`                                            | `⟪x, y⟫_ℝ`      | `open scoped InnerProductSpace`               |
| `inner _ x y` (no subscript, 𝕜 inferred)                 | `⟪x, y⟫`        | `open scoped RealInnerProductSpace` or `ComplexInnerProductSpace` depending on 𝕜 |
| `Finset.sum Finset.univ (fun i => f i)`                  | `∑ i, f i`      | `open BigOperators` (usually already implicit) |
| `Finset.prod Finset.univ (fun i => f i)`                 | `∏ i, f i`      | `open BigOperators`                           |
| `norm x` *(function-call form)*                          | `‖x‖`           | none — `‖·‖` is global                        |
| `Complex.I`                                              | `I`             | `open Complex` / `open scoped Complex`        |
| `Real.pi`                                                | `π`             | `open Real` / `open scoped Real`              |
| `ContinuousLinearMap.comp f g`                           | `f ∘L g`        | none — `∘L` is the canonical infix form       |
| `f.comp g` (ContinuousLinearMap dot-form)                | `f ∘L g`        | **default-apply**: dot-form is idiomatic Lean but the paper form is `∘L` in operator-algebra contexts |
| `ContinuousLinearMap.adjoint f` / `f.adjoint`            | `f†`            | `open scoped Adjoint` (where exported by Mathlib version) |
| `star a`                                                 | `a⋆`            | `open scoped ComplexConjugate` (for ℂ)        |

Scope note: Mathlib puts the **subscripted** inner-product bracket
`⟪x, y⟫_𝕜` in the generic `InnerProductSpace` scope
(`Mathlib/Analysis/InnerProductSpace/Defs.lean ~:86`). The field-specific
scopes `RealInnerProductSpace` and `ComplexInnerProductSpace` only
provide the **bare** `⟪x, y⟫` with the field inferred. Choose the scope
based on the paper form you want — if `⟪x, y⟫_ℂ` is the target, open
`InnerProductSpace`; if `⟪x, y⟫` (no subscript, field inferred) is
acceptable, open `ComplexInnerProductSpace` instead.

See `references/notation-map.md` for the exhaustive table, precedence
quirks, and cases where the scope would re-export too much and should be
kept local.

### Mode B — reference-paper-driven domain notation

When a declaration is a named object in the literature but has no
Mathlib notation (e.g. `quantumRelativeEntropy`, `gnsRepresentation`,
`modularOperator`), the skill does **not** invent a rendering from its
own knowledge. Instead, it consumes the project's ingested paper
knowledge base under `<cwd>/references/<slug>/` — the output of
`pdf-to-knowledge` / `web-to-knowledge` — and extracts the paper's own
symbol. The paper is the source of truth.

Workflow:

1. **Identify the concept.** The user names the declaration directly
   ("add paper notation for `quantumRelativeEntropy`"), or gives a
   file and the skill enumerates likely domain concepts (`noncomputable
   def` whose docstring cites a paper or names a textbook symbol).

2. **Locate the paper.** In priority order:
   a. The declaration's docstring already cites one (e.g. "See Araki
      1976" or "from Nielsen–Chuang §11.4").
   b. The user names one in the invocation.
   c. Fall back: list `<cwd>/references/*/` and ask the user which to
      search.

3. **Open the paper under `references/<slug>/` and extract the
   canonical symbol.** Sources in priority order:
   a. `INDEX.md` → "Key concepts" section — often pins the exact
      symbol the paper uses.
   b. `content.md` (for short papers) or `sections/*.md` (long ones) —
      grep for the concept's English name(s) and capture the nearest
      LaTeX formula (`$...$` or `$$...$$`).
   c. Handle spelling variants explicitly — a paper may use
      `D(\rho \| \sigma)`, `D(\rho \parallel \sigma)`, `S(\rho | \sigma)`,
      or `D(\rho || \sigma)`. Use **the spelling the cited paper uses**;
      never silently normalise across papers.

4. **Translate LaTeX to Unicode.** Common mappings: `\rho → ρ`,
   `\sigma → σ`, `\omega → ω`, `\Delta → Δ`, `\pi → π`, `\Omega → Ω`,
   `\| → ‖`, `\parallel → ‖`, `\otimes → ⊗`, `\oplus → ⊕`. The full
   table lives in `references/notation-map.md`.

5. **Design matching Lean notation.** Same rules as before:
   - Colocate with the definition; use a namespace that matches the
     concept.
   - Default to `scoped notation` inside that namespace so importers
     opt in via `open scoped …`. Use global `notation` only when the
     symbol is universally unambiguous (rare in physics).
   - **Set placeholder precedence to `:max`** whenever a separator
     token inside the notation is also a Lean operator (`‖`, `|`, `⟨`,
     `⟩`, `*`, `^`, …). Without `:max` the term parser keeps reading
     past the separator looking for a matching close-bracket.

     ```lean
     -- Correct — placeholders restricted to max-precedence terms
     scoped notation "D(" ρ:max " ‖ " σ:max ")" => quantumRelativeEntropy ρ σ
     ```

     Naive (without `:max`) fails with
     `unexpected token ')'; expected '‖', '‖₊' or '‖ₑ'` because `‖ σ ")"`
     is parsed as the inside of `‖·‖`.

   - **Multi-token mixfix** (e.g. `D(_ ‖ _)`, `⟪_ | _⟫_ω`, `π_ω`,
     `Tr_B`) that plain `scoped notation` can't handle cleanly goes
     through `syntax` + `macro_rules`. Remember to also provide an
     `app_unexpander` so the pretty-printer can round-trip:

     ```lean
     syntax:100 "D(" term:max " ‖ " term:max ")" : term
     macro_rules | `(D( $ρ ‖ $σ )) => `(quantumRelativeEntropy $ρ $σ)
     @[app_unexpander quantumRelativeEntropy]
     meta def quantumRelativeEntropy.unexpander : Lean.PrettyPrinter.Unexpander
       | `($_ $ρ $σ) => `(D( $ρ ‖ $σ ))
       | _ => throw ()
     ```

     Note: `meta def` (not plain `def`) may be required if the file is
     under `module` / `@[expose] public section`.

   - **Check for collisions** via `lean_loogle` / `lean_leansearch`
     before committing a symbol. Shadowing a Mathlib symbol breaks
     downstream files silently.

6. **Pin the result with `#guard_msgs`.** Always round-trip against
   the symbol extracted from the paper verbatim. If the pp output
   differs, the build fails — this is Layer 2 of the verification.

   ```lean
   /-- info: D(ρ ‖ σ) : ℝ -/
   #guard_msgs in #check (D(ρ ‖ σ) : ℝ)
   ```

7. **Record provenance.** The notation declaration gets a docstring
   citing the `references/<slug>/…` path *and* (if available) a
   specific section, page, or heading anchor. This is what lets a
   future reader trace the symbol back to the paper.

8. **Add a companion `Coe` if paper notation hides a type gap.** Papers
   often elide the distinction between a bundled subtype (e.g.
   `DensityMatrix A`) and its underlying carrier (`A`). If the notation
   only type-checks after such a coercion, add:

   ```lean
   instance : Coe (DensityMatrix A) A := ⟨DensityMatrix.toAlg⟩
   ```

   Gate on: (a) the target type has a unique canonical embedding,
   (b) no existing `Coe`-style instance already covers it (check via
   `lean_loogle` for `Coe X Y`), (c) the coercion is monomorphic (no
   implicit typeclass arguments that could conflict). If any gate
   fails, keep the long-form call and flag it in `report.md`.

### Worked Mode-B example — quantum relative entropy from `references/araki-1976/`

Suppose the user says "add paper notation for `quantumRelativeEntropy`
using `references/araki-1976/`". The skill:

1. Opens `references/araki-1976/INDEX.md` → `Key concepts` and finds
   the entry `Relative entropy $D(\rho \| \sigma)$ — defined in §2`.
2. Opens `references/araki-1976/content.md` §2 and greps for the
   formula. Captures `$D(\rho \| \sigma) = \mathrm{Tr}(\rho (\log \rho - \log \sigma))$`.
3. Translates to Unicode: `D(ρ ‖ σ) = Tr(ρ(log ρ − log σ))`.
4. Proposes notation + companion `Coe` + round-trip test.

Before:

```lean
namespace QuantumRelativeEntropy
variable {A : Type*} [CStarAlgebra A]

/-- Umegaki relative entropy. -/
noncomputable def quantumRelativeEntropy (ρ σ : A) : ℝ := …

lemma nonneg (ρ σ : DensityMatrix A) :
    0 ≤ quantumRelativeEntropy ρ.toAlg σ.toAlg := …
end QuantumRelativeEntropy
```

After (placeholder-at-`:max` precedence form, the skill's default):

```lean
namespace QuantumRelativeEntropy
variable {A : Type*} [CStarAlgebra A]

/-- Umegaki relative entropy. See `references/araki-1976/content.md`
§2 for the definition this notation mirrors. -/
noncomputable def quantumRelativeEntropy (ρ σ : A) : ℝ := …

/-- Density matrices coerce into the ambient algebra so paper notation
like `D(ρ ‖ σ)` elaborates without explicit `.toAlg` unfolds. -/
instance : Coe (DensityMatrix A) A := ⟨DensityMatrix.toAlg⟩

/-- Paper notation for Umegaki relative entropy as written in Araki
1976, §2 (see `references/araki-1976/content.md`). Open
`scoped QuantumRelativeEntropy` to use. -/
scoped notation "D(" ρ:max " ‖ " σ:max ")" => quantumRelativeEntropy ρ σ

/-- info: D(ρ ‖ σ) : ℝ -/
#guard_msgs in
example (ρ σ : DensityMatrix A) :
    @id ℝ (D(ρ ‖ σ)) = quantumRelativeEntropy (ρ : A) (σ : A) := rfl

lemma nonneg (ρ σ : DensityMatrix A) : 0 ≤ D(ρ ‖ σ) := …
end QuantumRelativeEntropy
```

If the placeholders bump into Lean's parser for other reasons (nested
mixfix, exponents, subscripts), use the `syntax` + `macro_rules` +
`app_unexpander` form instead — see step 5 above.

## Workflow

1. **Read the target.** Note existing `import`, `open`, `open scoped`
   lines at the top. Keep a running list of already-opened scopes so
   you don't double-open.
2. **Mode A pass.** Grep for each long-form pattern. For each hit, check
   whether the required scope is already open. If not, prefer adding
   `open scoped <Namespace>` at the file top to opening the whole
   namespace (smaller blast radius). If adding the scope would re-export
   types or instances that could conflict with local definitions, keep
   the long form and note it.
3. **Mode B pass.** Scan for domain-concept identifiers that have a
   textbook rendering. For each:
   1. Use `lean_loogle` to check Mathlib for existing notation.
   2. Identify the paper (docstring citation, user direction, or list
      `references/` and ask). Open it under `references/<slug>/`.
   3. Extract the canonical symbol verbatim from `INDEX.md` / `content.md`
      / `sections/*.md` (grep + nearest LaTeX formula).
   4. Translate LaTeX to Unicode and apply the precedence / `syntax` /
      `macro_rules` rules per Mode B step 5.
   5. Propose the notation + companion `Coe` if needed; cite the
      paper path in the notation's docstring.
4. **Apply changes one declaration at a time.** After each change call
   `lean_diagnostic_messages` on the file. If red, revert just that
   change and continue with the next candidate.
5. **Full build gate.** After all changes, `lake build <touched
   modules>` must pass with no new warnings.
6. **Axiom hygiene.** Run `lean_verify` on at least one representative
   theorem in each touched file. Notation rewrites should never
   introduce new axioms, but the check is cheap.
7. **Round-trip test for Mode B.** Append a `#guard_msgs` block (or
   equivalent `#check` comparison) that pins the pretty-printed form to
   the new notation. This is the single most important check — it is
   what confirms a *human reader* sees the new form, not just that the
   source text contains the new tokens.
8. **Emit `report.md`** in the workspace directory listing:
   - Mode A rewrites applied (file:line, before → after).
   - Mode B notation + coercions added (declaration, chosen symbol,
     paper reference).
   - Candidates deliberately skipped, with the reason (scope conflict,
     coercion gate failed, precedence too fragile, user declined).

## Guardrails

- Never write `sorry`, `admit`, `axiom`, `set_option`, `unsafe`, or touch
  `System` / `Lean.Elab` / `Lean.Meta`. `CLAUDE.md` in the repo root
  forbids all of these. If the skill thinks it needs any of them, it
  has strayed out of scope — stop and ask.
- Never modify `lakefile.toml`, `lean-toolchain`, or `lake-manifest.json`.
- Never create namespaces named `QuantumSystem` (the module path
  already prefixes every declaration).
- Spaces only, 100-column limit, English comments.
- One logical change per commit if the user asks for a commit.

## References

- `references/notation-map.md` — full Mode A mapping table, Mode B
  cheat sheet (operator algebra, quantum information, modular theory),
  `syntax` / `macro_rules` templates, precedence conventions.
