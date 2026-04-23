#!/usr/bin/env python3
"""PostToolUse hook: refresh ``references/CONCEPTS.md`` after an INDEX.md edit.

Wired from ``.claude/settings.json`` via:

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

See ``hooks/README.md`` for the rationale behind the ``sh -c`` wrapper
(CLAUDE_PROJECT_DIR portability + graceful disable when the script is
removed). The hook is deliberately permissive:

- It exits 0 on any exception so a bad hook never blocks Claude's edit.
- It ignores edits that do not target a ``references/<slug>/INDEX.md``.
- It does nothing when the edited INDEX.md is inside a skill snapshot or
  test-iteration tree (``skill-creator-tests/`` / ``iteration-*/``) — those
  dirs contain frozen fixtures that should not auto-refresh.
- Output goes to stderr so the user sees "[concepts-hook] regenerated ..."
  inline with their session.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path


SKIP_PARTS = frozenset({"skill-snapshot", "gap-filler-snapshot", "web-to-knowledge-snapshot"})
SKIP_PREFIXES = ("iteration-", "iter-")


def _is_index_md(path: Path) -> bool:
    return path.name == "INDEX.md" and any(p.name == "references" for p in path.parents)


def _is_fixture(path: Path) -> bool:
    parts = set(path.parts)
    if parts & SKIP_PARTS:
        return True
    # Skip iteration-N style test artefacts so regenerated CONCEPTS.md does
    # not disturb frozen eval outputs.
    for parent in path.parents:
        if parent.name.startswith(SKIP_PREFIXES) and parent.parent.name == "skill-creator-tests" or (
            parent.name == "skill-creator-tests"
        ):
            return True
    return False


def _references_root(path: Path) -> Path | None:
    """Return the ``references/`` directory that owns this INDEX.md, or None."""
    for parent in path.parents:
        if parent.name == "references":
            return parent
    return None


def _run_update_concepts(root: Path) -> None:
    script = (
        Path(__file__).resolve().parents[1] / "scripts" / "update_concepts.py"
    )
    try:
        result = subprocess.run(
            ["python3", str(script), str(root)],
            capture_output=True,
            text=True,
            timeout=30,
        )
    except Exception as exc:
        print(f"[concepts-hook] failed to invoke update_concepts.py: {exc}", file=sys.stderr)
        return
    message = (result.stdout or result.stderr).strip().splitlines()
    for line in message[-3:]:
        print(f"[concepts-hook] {line}", file=sys.stderr)


def main() -> int:
    try:
        payload = json.load(sys.stdin)
    except (json.JSONDecodeError, OSError):
        return 0

    tool_input = payload.get("tool_input") or {}
    raw = tool_input.get("file_path") or ""
    if not raw:
        # Edit/Write with no resolvable path — nothing to do.
        return 0

    path = Path(raw)
    if not path.is_absolute():
        cwd = payload.get("cwd") or os.getcwd()
        path = (Path(cwd) / path).resolve()
    else:
        path = path.resolve()

    if not _is_index_md(path):
        return 0
    if _is_fixture(path):
        return 0

    root = _references_root(path)
    if root is None or not root.is_dir():
        return 0

    _run_update_concepts(root)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        # Hook must never block the session on its own errors.
        print(f"[concepts-hook] unexpected error: {exc}", file=sys.stderr)
        raise SystemExit(0)
