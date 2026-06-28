---
name: math-review
description: Run the mathematician/physicist code review (the `math-reviewer` agent) over explicitly named Lean files or directories — statement fidelity, unfamiliar or deferred structures and hypotheses, and readable notation.
disable-model-invocation: true
---

# math-review

Run the math/physics review on a target the user names explicitly. This skill
only **resolves the target and dispatches** to the `math-reviewer` agent — the
review methodology (the four axes, the elaborated-type discipline, the output
format) lives in `.claude/agents/math-reviewer.md`, never duplicate it here.

## Steps

1. **Resolve the target.** Take the file or directory paths from the request
   (arguments to the skill, or the paths the user names). Expand each directory
   to the `.lean` files under it with Glob; keep explicit file paths as given.
   If no path is supplied, ask which file or directory to review — do not guess.
   *Done when:* you hold a concrete, non-empty list of `.lean` files to review.

2. **Dispatch to the `math-reviewer` agent.** Launch the `math-reviewer` agent
   (via the Agent tool, `subagent_type: math-reviewer`) on the resolved target:
   - A handful of related files → one `math-reviewer` invocation covering the set.
   - Many files → one `math-reviewer` per file (or per cohesive module), in parallel
     (multiple Agent calls in a single message).
   Pass the exact file paths in the prompt and instruct the agent to review only
   those. Do not re-implement the review yourself; the agent owns the axes.
   *Done when:* every resolved file is covered by a dispatched `reviewer` run.

3. **Report.** Relay the agents' findings to the user, grouped by file. Preserve
   each finding's `file:line` reference, fact/inference label, and severity as
   the agent returned them; do not soften or drop findings. If a run found no
   issues for a file, say so.
   *Done when:* the user has the consolidated findings for every reviewed file.
