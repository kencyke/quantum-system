# notation-map.md

Reference for `paper-notation-refactor`. Two parts:

- **Part 1** — Mode A static mapping table of Mathlib-staple
  conversions the skill applies without external input.
- **Part 2** — Mode B crib sheet + recipes for extracting symbols
  from the project's ingested reference material under
  `<cwd>/references/<slug>/`.

Read this file whenever `SKILL.md`'s inline table does not cover the
pattern at hand, or when deciding how to shape a new `scoped notation`
block.

## Part 1 — Mode A mapping table (apply existing Mathlib notation)

### Inner product

| long form                                        | paper form     | scope to open                             |
| ------------------------------------------------ | -------------- | ----------------------------------------- |
| `inner ℂ x y`                                    | `⟪x, y⟫_ℂ`     | `open scoped InnerProductSpace`           |
| `inner ℝ x y`                                    | `⟪x, y⟫_ℝ`     | `open scoped InnerProductSpace`           |
| `inner 𝕜 x y`                                    | `⟪x, y⟫_𝕜`     | `open scoped InnerProductSpace`           |
| `inner _ x y` (no subscript)                     | `⟪x, y⟫`       | `open scoped RealInnerProductSpace` or `ComplexInnerProductSpace` depending on `𝕜` |

Caveats:
- In Mathlib, the **subscripted** form `⟪x, y⟫_𝕜` lives in the
  generic `InnerProductSpace` scope
  (`Mathlib/Analysis/InnerProductSpace/Defs.lean ~:86`). The
  field-specific scopes `RealInnerProductSpace` and
  `ComplexInnerProductSpace` only define the **bare** `⟪x, y⟫` (field
  inferred). This is the opposite of what the naming might suggest —
  double-check when choosing a scope.
- Pick the scope based on the paper form you want:
  - `⟪x, y⟫_ℂ` (subscript visible) → `open scoped InnerProductSpace`
  - `⟪x, y⟫` (subscript hidden) → `open scoped ComplexInnerProductSpace`
    or `RealInnerProductSpace`
- If the file already uses `⟪·, ·⟫_𝕜` explicitly (with subscript),
  don't collapse to the bare `⟪·, ·⟫` — the explicit form is clearer
  at call sites and matches most textbook conventions.

### Sums, products, finite set operations

| long form                                         | paper form        | scope                            |
| ------------------------------------------------- | ----------------- | -------------------------------- |
| `Finset.sum Finset.univ (fun i => f i)`           | `∑ i, f i`        | `open BigOperators` (default on) |
| `Finset.prod Finset.univ (fun i => f i)`          | `∏ i, f i`        | `open BigOperators`              |
| `Finset.sum S (fun i => f i)`                     | `∑ i ∈ S, f i`    | `open BigOperators`              |
| `Finset.prod S (fun i => f i)`                    | `∏ i ∈ S, f i`    | `open BigOperators`              |
| `∑ i, f i` where `i : Fin n`                      | keep as is        | already paper form               |

Caveats:
- Mathlib auto-opens `BigOperators` in most analytic files; check the
  file's imports before adding an explicit `open BigOperators`.
- Do NOT rewrite `Finset.sum S f` when `f` is a bare named function; the
  paper form `∑ i ∈ S, f i` is only a win when the summand body is
  non-trivial.

### Norms, absolute values

| long form         | paper form     | scope                                          |
| ----------------- | -------------- | ---------------------------------------------- |
| `norm x`          | `‖x‖`          | global (`Norm` typeclass)                      |
| `‖x‖₊`            | `‖x‖₊`         | keep (nonneg-reals norm, distinct symbol)      |
| `dist x y`        | `dist x y`     | keep — no Unicode standard                     |
| `abs x`           | `|x|`          | `open scoped Int.Abs` (for `ℤ`), or mathlib's default |
| `Complex.abs z`   | `|z|`          | after `open Complex` — global `|·|` works on ℂ |

### Adjoint, star, involution

| long form                            | paper form    | scope                                 |
| ------------------------------------ | ------------- | ------------------------------------- |
| `ContinuousLinearMap.adjoint f`      | `f†`          | `open scoped Adjoint` (if exported)   |
| `LinearMap.adjoint f`                | `f†`          | same                                  |
| `star a`                             | `a⋆`          | `open scoped ComplexConjugate`        |
| `(starRingEnd ℂ) z`                  | `conj z` or `z̄` | `open scoped ComplexConjugate`      |

Caveats:
- `†` notation in Mathlib is currently scoped and changes occasionally
  across mathlib versions; if `open scoped Adjoint` is unknown, fall
  back to `f.adjoint` (still more paper-like than
  `ContinuousLinearMap.adjoint f`).
- `star` vs `⋆` — some files prefer the word form for grepability.
  Respect existing file conventions; only rewrite a `star` to `⋆`
  when the file already has other `⋆` usages, or when the user
  explicitly asks.

### Complex / real scalars

| long form         | paper form  | scope                                     |
| ----------------- | ----------- | ----------------------------------------- |
| `Complex.I`       | `I`         | `open Complex` / `open scoped Complex`    |
| `Complex.ofReal x` | `(x : ℂ)`  | ascription — use when context is a term   |
| `Real.pi`         | `π`         | `open Real` / `open scoped Real`          |
| `Real.exp x`      | `exp x`     | `open Real`                               |
| `Real.log x`      | `log x`     | `open Real`                               |
| `Real.sqrt x`     | `√x`        | only if `open Real` AND `√` is in scope   |

Caveats:
- `I` is a short identifier that can shadow local variables named `I`;
  check the file first. If there's a local `I`, leave `Complex.I` alone.
- `Complex.ofReal x` written explicitly is sometimes used for
  disambiguation. Only collapse to `(x : ℂ)` when the surrounding
  context makes the target type unambiguous.

### Linear maps, operators, algebras

| long form                                         | paper form                       | scope / notes                  |
| ------------------------------------------------- | -------------------------------- | ------------------------------ |
| `ContinuousLinearMap.id ℂ H`                      | `(1 : H →L[ℂ] H)` or `id`        | contextual                     |
| `LinearMap.comp f g`                              | `f ∘ₗ g`                         | infix `∘ₗ` ships globally      |
| `ContinuousLinearMap.comp f g`                    | `f ∘L g`                         | infix `∘L` ships globally      |
| `f.comp g` (ContinuousLinearMap dot-form)         | `f ∘L g`                         | **default-apply**: dot-form is idiomatic Lean; `∘L` is the paper form in operator-algebra |
| `g.comp (h.comp k)` / `(g.comp h).comp k`         | `g ∘L h ∘L k`                    | default-apply; `∘L` is right-associative in Mathlib, but the pp form matches papers |
| `HPow.hPow x n` (numeric literal)                 | `x ^ n`                          | global                         |
| `SMul.smul c x`                                   | `c • x`                          | global                         |

Caveats for `.comp` → `∘L`:

- **Do** apply the rewrite by default when the composed maps are
  continuous linear maps over a common field. This was the iteration-1
  miss — the skill was too conservative about "dot-notation is
  idiomatic" and left `.comp` in place even though `∘L` is what a
  paper would show. Default policy: **apply unless there's a specific
  reason not to**.
- **Skip** the rewrite when:
  - The dot-form call-chain is mixed with non-`ContinuousLinearMap`
    `.comp` calls (e.g. `Function.comp`, category-theory composition).
    Silent retargeting would be wrong.
  - The `.comp` appears as part of a lemma *name* inside `simp [...]`
    (e.g. `ContinuousLinearMap.comp_apply`) — those are identifiers,
    not composition terms.
  - The composition is of two morphisms in an algebra whose paper form
    uses multiplication (`fg` juxtaposition), not `∘`. In that case
    the right paper form is `f * g`, not `f ∘L g`.

### Simp-only helpers that look like notation

Do **not** rewrite:
- `RCLike.ofReal`, `Complex.re`, `Complex.im` — these are functions, not
  notation; their long form is the canonical spelling.
- `NNReal.toReal`, `ENNReal.toReal`, `Rat.cast` — same reasoning.
- Field projections (`.re`, `.im`, `.1`, `.2`) — already compact.

## Part 2 — Mode B crib sheet + extraction from `references/<slug>/`

Mode B is **reference-paper-driven**: the skill reads the project's
ingested paper knowledge base under `<cwd>/references/<slug>/` (produced
by `pdf-to-knowledge` / `web-to-knowledge`) and uses the paper's own
rendering as the source of truth for Lean notation. The crib sheet
below is a fallback for papers the user has not ingested yet. When a
paper *is* ingested, prefer grepping its `content.md` over the
crib sheet.

### Extracting a symbol from an ingested paper

Input: a Lean declaration name (`quantumRelativeEntropy`), a
paper slug (`araki-1976`).

1. `Read <cwd>/references/<slug>/INDEX.md` → "Key concepts" section.
   Each key concept entry typically pins the exact paper symbol in
   LaTeX. If the concept is listed, you're done — copy its symbol and
   translate to Unicode (table below).

2. If not found in `INDEX.md`, fall back to the body:
   - Short paper: `Read <cwd>/references/<slug>/content.md` and `Grep`
     for the concept's English name and its close synonyms:
     - "relative entropy" | "quantum relative entropy" | "Umegaki"
     - "GNS representation" | "cyclic representation"
     - "modular operator" | "Tomita–Takesaki" | "Tomita"
     Capture the **first display formula** near each hit — LaTeX is
     delimited `$...$` (inline) or `$$...$$` (display).
   - Long paper: same, but in `sections/*.md` (pick the section whose
     name aligns with the concept).

3. Handle spelling variants. Do not silently normalise across papers:
   - `D(\rho \| \sigma)` vs `D(\rho \parallel \sigma)` vs
     `D(\rho || \sigma)` vs `S(\rho | \sigma)` — use whichever the
     cited paper uses. The notation's docstring cites which paper
     provided the spelling so a reader can diff.
   - `\mathrm{Tr}` vs `\mathop{\mathrm{tr}}` vs `\mathrm{tr}` —
     same story.

4. Translate LaTeX to Unicode using the table below. If the LaTeX uses
   a token this table doesn't cover, stop and ask the user rather than
   guessing.

### LaTeX → Unicode translation table

| LaTeX                 | Unicode | Notes                                  |
| --------------------- | ------- | -------------------------------------- |
| `\rho`                | `ρ`     |                                        |
| `\sigma`              | `σ`     |                                        |
| `\tau`                | `τ`     |                                        |
| `\omega`              | `ω`     |                                        |
| `\pi`                 | `π`     |                                        |
| `\Omega`              | `Ω`     |                                        |
| `\Delta`              | `Δ`     |                                        |
| `\Lambda`             | `Λ`     | commonly used for bounded regions in AQFT |
| `\alpha`              | `α`     |                                        |
| `\beta`               | `β`     |                                        |
| `\mathcal{H}`         | `H`     | often the Hilbert-space name           |
| `\mathcal{A}`         | `A`     | algebra / C*-algebra                   |
| `\mathcal{B}(H)`      | `𝓑(H)`  | bounded operators (this project uses the `𝓑` script-B) |
| `\mathcal{O}`         | `𝒪`     | U+1D4AA — AQFT double cone             |
| `\mathcal{N}`         | `𝒩`     | U+1D4A9 — net / nest                   |
| `\mathcal{F}`         | `𝓕`     | U+1D4D5 — Fourier / filtration         |
| `\mathcal{D}`         | `𝓓`     | U+1D4D3 — domain of an unbounded op    |
| `\mathfrak{A}`        | `𝔄`     | U+1D504 — Fraktur A, Haag–Kastler local algebra |
| `\mathfrak{F}`        | `𝔉`     | U+1D509 — Fraktur F, field net         |
| `\mathfrak{M}`        | `𝔐`     | U+1D510 — Fraktur M, von Neumann algebra |
| `\mathfrak{B}(H)`     | `𝔅(H)`  | U+1D505 — Fraktur B variant of bounded ops |
| `\|` / `\parallel`    | `‖`     | **same symbol as Lean norm** — use `:max` precedence on placeholders |
| `\otimes`             | `⊗`     |                                        |
| `\oplus`              | `⊕`     |                                        |
| `\dagger` / `^*`      | `†`     | adjoint — mathlib's `Adjoint` scope    |
| `\overline{X}` / `\bar{X}` | `X̄` | bar — Unicode combining macron        |
| `\langle X \rangle`   | `⟨X⟩`   | bracket                                |
| `\llbracket X \rrbracket` | `⟦X⟧` | double bracket                       |
| `\mathrm{Tr}`         | `Tr`    | keep ASCII, not a Unicode replacement  |
| `\log`, `\exp`, `\sin` | `log`, `exp`, `sin` | keep ASCII                 |
| `\le` / `\leq`        | `≤`     |                                        |
| `\neq`                | `≠`     |                                        |
| `\in`                 | `∈`     |                                        |
| `\subset` / `\subseteq` | `⊆`   |                                        |
| `\infty`              | `∞`     |                                        |
| `\sum`                | `∑`     |                                        |
| `\prod`               | `∏`     |                                        |
| `\int`                | `∫`     |                                        |

### Crib sheet — common symbols (starting point when no paper ingested)

| concept                    | typical paper form | starting Lean skeleton (verify against the user's chosen paper before using) |
| -------------------------- | ------------------ | ---------------------------------------------------------------------------- |
| quantum relative entropy   | `D(ρ ‖ σ)`         | `scoped notation "D(" ρ:max " ‖ " σ:max ")" => quantumRelativeEntropy ρ σ`   |
| von Neumann entropy        | `S(ρ)`             | `scoped notation "S(" ρ:max ")" => vonNeumannEntropy ρ`                      |
| GNS representation         | `π_ω`              | `syntax "π_" term:max : term` + `macro_rules | ``(π_$ω) => ``(gnsRepresentation $ω)` |
| GNS cyclic vector          | `Ω_ω`              | same pattern with `"Ω_"`                                                     |
| modular operator           | `Δ_ω`              | same pattern with `"Δ_"`                                                     |
| modular conjugation        | `J_ω`              | same pattern with `"J_"`                                                     |
| KMS state at `β`           | `ω_β`              | `syntax term:max "_β" : term` — NB: subscript `β` is fragile; some papers write `\omega^{(\beta)}` instead |
| partial trace over B       | `Tr_B`             | `syntax "Tr_" term:max : term` + `macro_rules`                               |
| partial transpose          | `ρ^{T_B}`          | `syntax term:max "^{T_" term:max "}" : term` + `macro_rules`                 |
| density-matrix fidelity    | `F(ρ, σ)`          | `scoped notation "F(" ρ:max ", " σ:max ")" => fidelity ρ σ`                  |
| trace distance             | `T(ρ, σ)`          | `scoped notation "T(" ρ:max ", " σ:max ")" => traceDistance ρ σ`             |
| commutator                 | `[A, B]` or `⟦A,B⟧` | `scoped notation "⟦" A:max ", " B:max "⟧" => commutator A B`                 |
| anti-commutator            | `{A, B}`           | avoid — collides with set-builder. Use `⦃A, B⦄` instead                      |

**Always check the actual paper first.** The crib sheet assumes the
common Araki / Umegaki / Nielsen–Chuang spellings, but (for example)
some textbooks use `S(ρ|σ)` instead of `D(ρ‖σ)` for the same object.
The skill must not silently pick one when the user's paper uses the
other.

### Lexer gotcha — subscripted prefixes like `α_g`, `π_ω`

Lean's lexer treats `α_g` (a letter followed by `_` and more letters) as a
**single identifier**, not as `α` + `_g`. `notation "α_" g:max` and similar
attempts therefore fail with `unexpected token ')'` or `expected term`. A
stand-alone numeric subscript (`α_0`) is fine because digits terminate the
identifier lex, but identifier-like subscripts (`g`, `ω`, `β`) will never
parse.

**Escape hatch:** use a bracketed form instead.

```lean
-- Works: brackets delimit the subscript cleanly
scoped syntax:max "α[" term "]" : term
scoped macro_rules | `(α[ $g ]) => `(gaugeAction $g)

-- Also works: dedicated two-token form with a visible space
scoped notation:max "α " g:max => gaugeAction g
```

Apply the same rule to `π_ω`, `Ω_ω`, `Δ_ω`, `J_ω`, `ω_β`: whenever the
subscript is another identifier, use `π[ω]` / `Ω[ω]` / `Δ[ω]` / `ω[β]` or
an explicit space. The crib sheet flags these as "fragile" for exactly
this reason.

### `meta def` is mandatory inside `module` / `@[expose] public section`

Every file under `QuantumSystem/` starts with `module` plus
`@[expose] public section` (and any fixture that mimics that header
inherits the constraint). Under that header, the pretty-printer
unexpander **must** be declared as `meta def`, not `def`:

```lean
@[app_unexpander quantumRelativeEntropy]
meta def quantumRelativeEntropy.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $ρ $σ) => `(D( $ρ ‖ $σ ))
  | _ => throw ()
```

A plain `def` under this header fails with `declaration must be marked
as 'meta'`. This is true for every Mode B unexpander in this project.

### Round-trip template

Always add a `#guard_msgs` block in the same file as the notation
declaration. This is Layer 2 of the verification:

```lean
/-- info: D(ρ ‖ σ) : ℝ -/
#guard_msgs in #check (D(ρ ‖ σ) : ℝ)
```

If the pretty-printer output differs from the string in the
`/-- info: ... -/` block, the build fails — catching both `notation`
parse errors and unexpander bugs in one check.

### Picking the right construct



| use case                                    | Lean construct                     |
| ------------------------------------------- | ---------------------------------- |
| binary infix with one operator token        | `infixl:<prec>` / `infixr:<prec>`  |
| prefix with one token                       | `prefix:<prec>`                    |
| postfix with one token                      | `postfix:<prec>`                   |
| literal keyword + variables, no mixing      | `notation "…" => …`                |
| multiple keyword tokens interleaved with args, subscripts, or non-ASCII brackets | `syntax` + `macro_rules` |

Never use plain `notation` for mixfix patterns like `D(_ ‖ _)`,
`⟨_ | _⟩_ω`, `π_ω`, `Ω_ω`, or anything with a subscript attached to a
symbol — `syntax` + `macro_rules` is the only form that handles
precedence + whitespace + Unicode reliably.

### Precedence conventions (Mathlib)

| level | used for                                    |
| ----- | ------------------------------------------- |
| 20    | `∧`, `∨` (low-level logic)                  |
| 35    | `≤`, `<`, `=`, `≠`                          |
| 50    | `+`, `-`                                    |
| 65    | `*`, `/`, `∘`, `•`                          |
| 70    | `^`                                         |
| 75    | function application, unary prefixes        |
| max   | bracket-like constructs (`⟨_, _⟩`, `‖_‖`)   |

### Companion `Coe` instance checklist

Before adding `instance : Coe X Y := ⟨f⟩` alongside new notation, confirm:

1. **Canonical.** `f : X → Y` is the one-and-only canonical embedding.
   Two competing candidates (e.g. density matrix → operator vs density
   matrix → trace-class operator) means no coercion — keep the explicit
   `.toAlg` call.
2. **Total.** No side-conditions (`h : X.Positive`). If you need a
   hypothesis, make a separate named conversion, not a `Coe`.
3. **Monomorphic.** No typeclass arguments on `f` that could pick the
   wrong instance.
4. **Non-conflicting.** `lean_loogle Coe X Y` returns nothing; grep the
   target file for existing `toAlg` / `toOp` / etc. that would become
   redundant.
5. **`CoeHead` vs `CoeTC` vs `Coe`.** Default to plain `Coe`. Upgrade to
   `CoeHead` if the coercion must fire only at the head of an
   elaboration chain (e.g. to stop transitivity loops). `CoeTC` only
   when you explicitly want transitive closure.

If any check fails, **do not add the instance**. Keep the long form and
flag it in `report.md`.

### Colocation rule

Place the `scoped notation` block (and its companion `instance : Coe …`)
**immediately after the definition it refers to**, inside the same
namespace. This keeps the declaration, its notation, and its coercion
discoverable from a single file read. Do not scatter them across a
`Notation.lean` sidecar unless the file is already overflowing the
500-line soft limit.

### Paper-reference policy

Every new `notation` declaration gets a docstring citing where the symbol
comes from. Accepted citations:

- Araki, H. (1976). "Relative Entropy of States of von Neumann Algebras".
- Bratteli & Robinson, "Operator Algebras and Quantum Statistical
  Mechanics" vol I & II.
- Nielsen & Chuang, "Quantum Computation and Quantum Information".
- Reed & Simon, "Methods of Modern Mathematical Physics" I–IV.
- Takesaki, "Theory of Operator Algebras" I–III.
- Haag, "Local Quantum Physics".

For a symbol from a paper not listed above, the skill asks the user to
confirm the citation before adding the notation.
