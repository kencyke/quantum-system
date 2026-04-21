# pdf-to-knowledge hooks

`.claude/settings.json` wires a `PostToolUse` hook that auto-regenerates
`references/CONCEPTS.md` whenever an `INDEX.md` under a `references/` tree
is edited. The hook is optional — nothing else in the skill depends on it.

## Files

- `on_index_change.py` — the hook implementation (stdlib-only).
- `README.md` — this file.

## How the wiring works

`.claude/settings.json` contains:

```json
{
  "hooks": {
    "PostToolUse": [
      {
        "matcher": "Edit|Write|NotebookEdit",
        "hooks": [
          {
            "type": "command",
            "command": "sh -c 'script=\"${CLAUDE_PROJECT_DIR}/.claude/skills/pdf-to-knowledge/hooks/on_index_change.py\"; [ -f \"$script\" ] && exec python3 \"$script\" || exit 0'"
          }
        ]
      }
    ]
  }
}
```

Important details:

- **`$CLAUDE_PROJECT_DIR`** is provided by Claude Code in every hook
  subprocess. It resolves to the project root that contains `.claude/`,
  regardless of the editor's current working directory. The command
  does **not** hardcode `/workspaces/quantum-system` anywhere — copy
  this tree into another project and the hook continues to work without
  edits.
- **Existence guard** (`[ -f "$script" ]`): if the hook script has been
  moved or deleted, the shell exits 0 instead of erroring. The skill
  author can delete `hooks/on_index_change.py` to disable the
  behaviour without also editing `settings.json`.
- **`exec python3`**: replaces the shell process with the Python one,
  minimising PID churn.
- **POSIX `sh`**: no Bash-isms, so the command runs under any POSIX
  shell Claude Code picks.

## What the hook does

1. Reads the `PostToolUse` JSON payload from stdin.
2. Extracts `tool_input.file_path`.
3. If the path ends in `INDEX.md` and is under a `references/` directory,
   the hook invokes
   `.claude/skills/pdf-to-knowledge/scripts/update_concepts.py <references-root>`
   to rebuild `CONCEPTS.md`.
4. **Fixture paths are skipped** — edits under `skill-creator-tests/` or
   any `iteration-*/` ancestor do not trigger regeneration, so frozen
   eval outputs stay stable.
5. Any exception is caught and the script exits 0. The hook never blocks
   an Edit tool call on its own error.

## Portability / disabling

- **Move to a different project**: copy `.claude/skills/pdf-to-knowledge/`
  verbatim AND keep the `hooks.PostToolUse` stanza in the new project's
  `.claude/settings.json`. No path edits required.
- **Disable**: delete the `hooks` stanza from `.claude/settings.json`,
  or delete `hooks/on_index_change.py` itself (the existence guard
  makes this a clean no-op).
- **Debug**: add a one-liner inside `main()` that writes to
  `/tmp/hook.log`. The hook's stderr surfaces in the Claude Code
  transcript as `[concepts-hook]` lines.

## Limitations

- The hook relies on `$CLAUDE_PROJECT_DIR` being set. If a future
  Claude Code release drops that variable, the `[ -f "$script" ]`
  guard turns the hook into a no-op (exit 0) — no crash, but the
  auto-refresh stops silently. Monitor `CONCEPTS.md` freshness via
  `update_concepts.py --check-fresh` in that case.
- The hook runs on **every** `Edit|Write|NotebookEdit`. For files that
  are not INDEX.md, it returns early at step 2 above — one cheap
  stdin-JSON parse per tool call. If you notice hook latency, profile
  `update_concepts.py` on your references tree; it is stdlib-only and
  typically runs in < 200 ms.
