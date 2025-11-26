# AGENTS.md

## Important Instructions

- Do not add files.
- Do not remove files.
- Do not use `git checkout`and `git reset`.
- Do not use `python` command.
- Do not use `cat` to overwrite a file.
- Do not modify `lakefile.toml`.
- Never use `axiom` and `set_option` for any reason!
- When `lemma` or `thorem` is too long, devide it into multiple `lemma`s.
- Never give up simply because it is complicated or time-consuming; instead, try to implement the missing lemmas step by step.
- Use `$...$` or `$$...$$` for LaTeX math formatting in markdown.
- Use `conj` as complex conjugate when declaring `open ComplexConjugate`.
- Use `simp` when referring `try 'simp' instead of 'simpa'`.
- Fix indentation when referring `expected '{' or indented tactic sequence`.
- Do not use tabs. Use spaces instead.
- Continue to implement tasks in `PLANS.md` autonomously until the maximum number of requests is reached.
- Do not use builtin `fetch` tool to read web pages. Alternatively, try to use `read_url_content_as_markdown`.
- Use `lean-lsp` mcp server tools when searching Mathlib, analyzing codes, etc.
- Write comments in English.

## Style Guidelines

Try to follow https://leanprover-community.github.io/contribute/style.html except `header-and-imports` closely.
