# AGENTS.md

## Important Instructions

- Never use tabs. Use spaces instead.
- Never modify `lakefile.toml`.
- Never use `python`, `cat`, `git checkout`and `git reset`.
- Fix indentation when referring `expected '{' or indented tactic sequence`.
- Autonomously continue executing the tasks specified in `PLANS.md` until the maximum request limit is reached.
- Use `lean-lsp` mcp server tools when searching Mathlib, analyzing codes, etc.
- Write comments in English.
- Use `$...$` or `$$...$$` for LaTeX math formatting in markdown.
- Never create namespaces or sections named `QuantumSystem`.

## Prohibitions

The following tokens are strictly prohibited to use in this project:

- `sorry`
- `admit`
- `axiom`
- `set_option`
- `unsafe`
- `System`
- `open System`
- `Lean.Elab`
- `Lean.Meta`
- `Lean.Compiler`

## Style Guidelines

Try to follow

- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/doc.md
- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/naming.md
- https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/style.md
