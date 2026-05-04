#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Scan a ``references/`` tree and report which Key concepts are still gaps.

A concept is classified by looking at the annotation on its Key concepts
bullet across every ``<slug>/INDEX.md`` under the root:

- ``→ formalized: QuantumSystem.X.y`` → **formalized** (already proven in
  this repository — outranks ``resolved`` for prioritisation).
- ``→ mathlib: Mathlib.X.y`` → **resolved** (mathlib already has it).
- ``→ needs formalization`` → **gap** (no mathlib coverage).
- No annotation → **ambiguous** (treat as potential gap).

Concepts with the same normalised name coming from multiple sources are
merged; the aggregate classification picks the strongest tier present —
``formalized`` beats ``resolved`` beats ``partial`` beats ``gap`` beats
``ambiguous``. ``suspect`` (a mathlib annotation that ``verify_mathlib_refs.py``
flagged as ``[UNVERIFIED]``) is reported separately so a previously
trusted answer that turned out wrong is more visible than a fresh gap.

Optionally, ``--goals path/to/goals.yaml`` constrains the coverage score
to a fixed list of target concepts (the project's actual formalization
goals). Without ``--goals`` the universe is "every concept ingested under
references/" — useful for raw progress, but the denominator drifts as
new papers are added. With ``--goals`` the score answers the operative
question: "of the concepts I committed to formalize, what fraction is
done?". Goal concepts not yet present in any INDEX.md are classified as
``unknown`` and counted as gaps for the coverage formula.

Usage:
    python3 detect_gaps.py <references-root> [--target-slug SLUG]
                                             [--output gaps.json]

When ``--target-slug`` is given, the output keys `resolved`/`gaps` are
restricted to concepts that originate from that slug's INDEX.md; other
slugs' concepts appear under `other_knowledge` (useful context but not
what the caller is trying to formalise). When omitted, every slug is
treated symmetrically.

Exits 0 on success. Prints the JSON report to stdout unless ``--output``
is specified.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import sys
from collections import defaultdict
from pathlib import Path


KEY_CONCEPTS_HEADER = re.compile(r"^##\s+Key concepts\s*$", re.IGNORECASE)
NEXT_H2 = re.compile(r"^##\s+")
BULLET = re.compile(r"^\s*-\s+(.*)$")
LEADING_CODE = re.compile(r"^`([^`]+)`(.*)$")
MATHLIB_ANNOT = re.compile(r"→\s*mathlib\s*:", re.IGNORECASE)
FORMALIZED_ANNOT = re.compile(r"→\s*formalized\s*:", re.IGNORECASE)
NEEDS_FORMAL_ANNOT = re.compile(r"→\s*needs\s*formalization", re.IGNORECASE)
UNVERIFIED_MARKER = re.compile(r"\[UNVERIFIED\]", re.IGNORECASE)
LEAN_DECL_NAME = re.compile(r"^[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*$")


class GoalsValidationError(ValueError):
    """Raised when goals.yaml violates the supported contract."""


def _strip_front_annotation_markers(body: str) -> tuple[str, str]:
    """Split a Key concepts bullet body into (description, annotation)."""
    m = re.search(r"\s*→\s", body)
    if not m:
        return body.strip(), ""
    return body[: m.start()].strip(), body[m.start() :].strip()


# LaTeX command → Unicode character. Keeps the merge key stable whether the
# author wrote ``\alpha``, ``α``, or ``alpha``. Longest commands first so
# ``\infty`` beats ``\in`` and ``\Vert`` beats ``\V`` on the ordered walk.
LATEX_TO_UNICODE: dict[str, str] = {
    # Greek lowercase (most common).
    r"\alpha": "α", r"\beta": "β", r"\gamma": "γ", r"\delta": "δ",
    r"\epsilon": "ε", r"\varepsilon": "ε", r"\zeta": "ζ", r"\eta": "η",
    r"\theta": "θ", r"\vartheta": "θ", r"\iota": "ι", r"\kappa": "κ",
    r"\lambda": "λ", r"\mu": "μ", r"\nu": "ν", r"\xi": "ξ",
    r"\pi": "π", r"\varpi": "π", r"\rho": "ρ", r"\varrho": "ρ",
    r"\sigma": "σ", r"\varsigma": "σ", r"\tau": "τ", r"\upsilon": "υ",
    r"\phi": "φ", r"\varphi": "φ", r"\chi": "χ", r"\psi": "ψ",
    r"\omega": "ω",
    # Greek uppercase.
    r"\Gamma": "Γ", r"\Delta": "Δ", r"\Theta": "Θ", r"\Lambda": "Λ",
    r"\Xi": "Ξ", r"\Pi": "Π", r"\Sigma": "Σ", r"\Upsilon": "Υ",
    r"\Phi": "Φ", r"\Psi": "Ψ", r"\Omega": "Ω",
    # Math symbols the operator-algebra / QFT canon uses constantly.
    r"\infty": "∞",
    r"\partial": "∂",
    r"\nabla": "∇",
    r"\mathbb{N}": "ℕ", r"\mathbb{Z}": "ℤ", r"\mathbb{Q}": "ℚ",
    r"\mathbb{R}": "ℝ", r"\mathbb{C}": "ℂ", r"\mathbb{H}": "ℍ",
    r"\mathbb{F}": "𝔽", r"\mathbb{P}": "ℙ", r"\mathbb{E}": "𝔼",
    r"\mathbb{1}": "𝟙",
    r"\emptyset": "∅", r"\varnothing": "∅",
    r"\hbar": "ℏ", r"\ell": "ℓ",
    r"\dagger": "†", r"\star": "⋆",
    # Relations / operators often embedded in concept names.
    r"\le": "≤", r"\leq": "≤", r"\ge": "≥", r"\geq": "≥",
    r"\ne": "≠", r"\neq": "≠", r"\equiv": "≡",
    r"\subset": "⊂", r"\subseteq": "⊆",
    r"\supset": "⊃", r"\supseteq": "⊇",
    r"\in": "∈", r"\notin": "∉",
    r"\to": "→", r"\mapsto": "↦", r"\implies": "⇒",
    r"\Rightarrow": "⇒", r"\Leftarrow": "⇐", r"\Leftrightarrow": "⇔",
    r"\cup": "∪", r"\cap": "∩", r"\setminus": "∖",
    r"\times": "×", r"\otimes": "⊗", r"\oplus": "⊕", r"\odot": "⊙",
    r"\cdot": "·",
    # Norms / brackets commonly mangled across editors.
    r"\Vert": "‖", r"\|": "‖", r"\|\|": "‖",
    r"\langle": "⟨", r"\rangle": "⟩",
    # Spacing commands we just drop.
    r"\,": " ", r"\;": " ", r"\:": " ", r"\!": "", r"\~": " ",
}

# Unicode math symbols → ASCII-ish tokens so ``α`` / ``\alpha`` / ``alpha``
# all collapse to the same bucket. Applied after LATEX_TO_UNICODE, so it
# normalises both original Unicode text and LaTeX-derived Unicode.
UNICODE_TO_ASCII: dict[str, str] = {
    # Greek lowercase.
    "α": " alpha ", "β": " beta ", "γ": " gamma ", "δ": " delta ",
    "ε": " epsilon ", "ζ": " zeta ", "η": " eta ", "θ": " theta ",
    "ι": " iota ", "κ": " kappa ", "λ": " lambda ", "μ": " mu ",
    "ν": " nu ", "ξ": " xi ", "π": " pi ", "ρ": " rho ",
    "σ": " sigma ", "τ": " tau ", "υ": " upsilon ", "φ": " phi ",
    "ϕ": " phi ", "χ": " chi ", "ψ": " psi ", "ω": " omega ",
    # Greek uppercase.
    "Γ": " gamma ", "Δ": " delta ", "Θ": " theta ", "Λ": " lambda ",
    "Ξ": " xi ", "Π": " pi ", "Σ": " sigma ", "Υ": " upsilon ",
    "Φ": " phi ", "Ψ": " psi ", "Ω": " omega ",
    # Math symbols.
    "∞": " infty ", "∂": " partial ", "∇": " nabla ",
    "ℕ": " nat ", "ℤ": " int ", "ℚ": " rat ", "ℝ": " real ",
    "ℂ": " complex ", "ℍ": " quat ", "𝔽": " field ", "ℙ": " proj ",
    "𝔼": " expect ", "𝟙": " one ",
    "∅": " empty ", "ℏ": " hbar ", "ℓ": " ell ",
    "†": " dagger ", "⋆": " star ",
    "≤": " le ", "≥": " ge ", "≠": " ne ", "≡": " equiv ",
    "⊂": " subset ", "⊆": " subseteq ",
    "⊃": " supset ", "⊇": " supseteq ",
    "∈": " in ", "∉": " notin ",
    "→": " to ", "↦": " mapsto ", "⇒": " implies ",
    "⇐": " leftarrow ", "⇔": " iff ",
    "∪": " cup ", "∩": " cap ", "∖": " setminus ",
    "×": " times ", "⊗": " otimes ", "⊕": " oplus ", "⊙": " odot ",
    "·": " cdot ",
    "‖": " norm ", "⟨": " langle ", "⟩": " rangle ",
    # Punctuation variants that frequently appear in math identifiers.
    "–": "-", "—": "-",  # en-dash / em-dash → hyphen
}

# Sort LaTeX commands by descending length so longer matches win (``\Vert``
# before ``\V``, ``\mathbb{N}`` before ``\mathbb``).
_LATEX_ORDERED = sorted(LATEX_TO_UNICODE.items(), key=lambda kv: -len(kv[0]))


def _expand_latex(text: str) -> str:
    r"""Apply ``LATEX_TO_UNICODE`` in a single pass.

    Uses string replacement (not regex) because TeX command boundaries are
    semantic: ``\alpha2`` should still replace ``\alpha`` → ``α``, producing
    ``α2``. A regex with ``\b`` would miss that because ``\`` is not a word
    char to Python's regex engine, but pure substring replacement works.
    """
    for command, replacement in _LATEX_ORDERED:
        if command in text:
            text = text.replace(command, replacement)
    return text


def _unicode_to_ascii(text: str) -> str:
    for symbol, replacement in UNICODE_TO_ASCII.items():
        if symbol in text:
            text = text.replace(symbol, replacement)
    return text


def _normalise_concept(display: str) -> str:
    """Aggressive normalisation so concept names with different spellings merge.

    The merge key has to be stable across:

    - camelCase / PascalCase: ``Connes cocycle`` == ``ConnesCocycle``
    - punctuation: ``Connes cocycle`` == ``Connes.cocycle`` == ``connes-cocycle``
    - acronyms: ``TypeIIIFactor`` == ``Type III factor``
    - **LaTeX vs Unicode vs ASCII** (R1, iter-12):
      ``Type II_\\infty`` == ``Type II_∞`` == ``Type II_infty``
      ``S(\\phi\\Vert\\psi)`` == ``S(φ‖ψ)`` == ``S(phi norm psi)``

    Pipeline:
    0. Expand LaTeX commands to Unicode (``\\alpha`` → ``α``).
    1. Collapse Unicode math symbols to ASCII tokens (``α`` → `` alpha ``,
       ``‖`` → `` norm ``, ``∞`` → `` infty ``).
    2. Split camelCase / PascalCase boundaries with a space.
    3. Lowercase.
    4. Replace any run of non-alphanumeric characters with a single space.
    5. Collapse whitespace.
    """
    tokenised = _expand_latex(display)
    tokenised = _unicode_to_ascii(tokenised)
    # Split lower→upper (fooBar) and acronym→word (HTTPServer, TypeIIIFactor).
    tokenised = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", " ", tokenised)
    tokenised = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", " ", tokenised)
    tokenised = tokenised.lower()
    tokenised = re.sub(r"[^a-z0-9]+", " ", tokenised)
    return " ".join(tokenised.split())


def parse_key_concepts(md: str) -> list[dict]:
    """Yield ``{name, display, description, annotation, status}`` for each bullet.

    ``name`` is aggressively normalised so bullets differing only by
    punctuation (``Connes.cocycle`` vs ``Connes cocycle``) or case
    (``typeIIIFactor`` vs ``Type III factor``) merge in
    ``classify_across_slugs``.
    """
    lines = md.splitlines()
    inside = False
    entries: list[dict] = []
    for line in lines:
        if KEY_CONCEPTS_HEADER.match(line):
            inside = True
            continue
        if inside and NEXT_H2.match(line):
            break
        if not inside:
            continue
        bullet = BULLET.match(line)
        if not bullet:
            continue
        body = bullet.group(1).strip()
        if not body or body.startswith("<!--"):
            continue
        m = LEADING_CODE.match(body)
        if m:
            display = m.group(1).strip()
            rest = m.group(2).lstrip(" -—:").rstrip()
        else:
            display = body.split("—", 1)[0].split(":", 1)[0].split("(", 1)[0].strip()[:60]
            rest = body
        description, annotation = _strip_front_annotation_markers(rest)
        if FORMALIZED_ANNOT.search(annotation) and UNVERIFIED_MARKER.search(annotation):
            # A `→ formalized:` annotation that failed `verify_mathlib_refs.py`
            # — same treatment as a suspect mathlib annotation.
            status = "suspect"
        elif FORMALIZED_ANNOT.search(annotation):
            status = "formalized"
        elif MATHLIB_ANNOT.search(annotation) and UNVERIFIED_MARKER.search(annotation):
            # A mathlib annotation that failed `verify_mathlib_refs.py` — do
            # not trust it. Downstream prioritisation should treat this as a
            # gap that also flags the previous search result as wrong.
            status = "suspect"
        elif MATHLIB_ANNOT.search(annotation):
            status = "resolved"
        elif NEEDS_FORMAL_ANNOT.search(annotation):
            status = "gap"
        else:
            status = "ambiguous"
        entries.append(
            {
                "name": _normalise_concept(display),
                "display": display,
                "description": description,
                "annotation": annotation,
                "status": status,
            }
        )
    return entries


def _read_frontmatter_slug(md: str, fallback: str) -> str:
    """Cheap YAML-ish slug extractor (no pyyaml dep)."""
    in_front = False
    for line in md.splitlines():
        if line.strip() == "---":
            if not in_front:
                in_front = True
                continue
            break
        if in_front:
            m = re.match(r"^slug\s*:\s*(.+)$", line)
            if m:
                return m.group(1).strip().strip('"').strip("'")
    return fallback


# --- goals.yaml (bespoke YAML-subset parser, no PyYAML dep) ---
#
# Supported shape:
#
#   goals:
#     - id: gns-construction
#       description: "Cyclic representation π_ω …"
#       declarations:
#         - GNS.Representation
#         - GNS.Construction.isFaithful_iff_separating
#       concepts:
#         - "GNS representation"                       # bare string
#         - name: "Tomita-Takesaki modular operator"   # structured
#           sources:
#             - { slug: arxiv-2507.00900, anchor: { theorem: "2.3" } }
#             - { slug: 92737, anchor: { definition: "modular operator" } }
#
# What the parser handles:
# - Top-level ``goals:`` block list
# - Each goal is a block mapping with arbitrary keys
# - Block lists under any key (declarations, concepts, sources, …)
# - List items can be bare scalars, inline flow mappings ``{ ... }``,
#   or block mappings introduced by ``- key: value``
# - Single-line inline flow mappings nest (``{ slug: a, anchor: { ... } }``)
#
# Indentation is taken at face value; 2-space steps are conventional but
# not enforced. The parser handles YAML-style inline comments and simple
# block scalars (`>` / `>-` / `|` / `|-`) because the checked-in
# goals.yaml uses them. It does not handle YAML anchors/tags/merge keys.


_INLINE_KEY_RE = re.compile(r"\s*([A-Za-z_][\w-]*)\s*:\s*")


def _strip_quote(value: str) -> str:
    value = value.strip()
    if (value.startswith('"') and value.endswith('"')) or (
        value.startswith("'") and value.endswith("'")
    ):
        return value[1:-1]
    return value


def _coerce_scalar(text: str):
    """Best-effort YAML scalar coercion (string / int / float / bool / null)."""
    text = text.strip()
    if not text:
        return None
    if (text.startswith('"') and text.endswith('"')) or (
        text.startswith("'") and text.endswith("'")
    ):
        return text[1:-1]
    if text in ("null", "~"):
        return None
    if text == "true":
        return True
    if text == "false":
        return False
    try:
        return int(text)
    except ValueError:
        pass
    try:
        return float(text)
    except ValueError:
        pass
    return text


def _strip_inline_comment(text: str) -> str:
    """Drop YAML-style inline comments while preserving quoted/flow content."""
    out: list[str] = []
    in_single = False
    in_double = False
    brace_depth = 0
    bracket_depth = 0
    for idx, ch in enumerate(text):
        if ch == "'" and not in_double:
            in_single = not in_single
            out.append(ch)
            continue
        if ch == '"' and not in_single:
            in_double = not in_double
            out.append(ch)
            continue
        if not in_single and not in_double:
            if ch == "{":
                brace_depth += 1
            elif ch == "}" and brace_depth > 0:
                brace_depth -= 1
            elif ch == "[":
                bracket_depth += 1
            elif ch == "]" and bracket_depth > 0:
                bracket_depth -= 1
            elif (
                ch == "#"
                and brace_depth == 0
                and bracket_depth == 0
                and (idx == 0 or text[idx - 1].isspace())
            ):
                break
        out.append(ch)
    return "".join(out).rstrip()


def _is_block_scalar_marker(text: str) -> bool:
    text = text.strip()
    return bool(text) and text[0] in ">|" and set(text[1:]) <= {"-", "+"}


def _fold_block_scalar(lines: list[str], marker: str) -> str:
    stripped = [line.strip() for line in lines]
    if not stripped:
        return ""
    if marker.startswith("|"):
        return "\n".join(stripped)
    return " ".join(part for part in stripped if part)


def _read_inline_value(s: str, pos: int):
    """Read a single value (quoted string, nested flow mapping, flow list,
    or bare scalar up to the next comma) from ``s`` starting at ``pos``.
    Returns ``(value, new_pos)``."""
    n = len(s)
    while pos < n and s[pos] == " ":
        pos += 1
    if pos >= n:
        return None, pos
    if s[pos] == "{":
        depth = 1
        start = pos
        pos += 1
        while pos < n and depth > 0:
            if s[pos] == "{":
                depth += 1
            elif s[pos] == "}":
                depth -= 1
            pos += 1
        return _parse_inline_mapping(s[start:pos]), pos
    if s[pos] == "[":
        depth = 1
        start = pos
        pos += 1
        while pos < n and depth > 0:
            if s[pos] == "[":
                depth += 1
            elif s[pos] == "]":
                depth -= 1
            pos += 1
        return _parse_inline_list(s[start:pos]), pos
    if s[pos] in '"\'':
        quote = s[pos]
        pos += 1
        start = pos
        while pos < n and s[pos] != quote:
            pos += 1
        value = s[start:pos]
        if pos < n:
            pos += 1
        return value, pos
    start = pos
    while pos < n and s[pos] != ",":
        pos += 1
    return _coerce_scalar(s[start:pos]), pos


def _parse_inline_mapping(text: str) -> dict:
    """Parse a YAML flow mapping like ``{ a: b, c: { d: e } }``."""
    text = text.strip()
    if not (text.startswith("{") and text.endswith("}")):
        raise ValueError(f"expected inline mapping: {text!r}")
    inner = text[1:-1]
    result: dict = {}
    pos = 0
    n = len(inner)
    while pos < n:
        while pos < n and inner[pos] in " ,":
            pos += 1
        if pos >= n:
            break
        m = _INLINE_KEY_RE.match(inner, pos)
        if not m:
            raise ValueError(f"missing key at pos {pos} in {text!r}")
        key = m.group(1)
        pos = m.end()
        value, pos = _read_inline_value(inner, pos)
        result[key] = value
    return result


def _parse_inline_list(text: str) -> list:
    """Parse a YAML flow list like ``[a, b, "c", {d: e}]``. Empty ``[]`` → ``[]``."""
    text = text.strip()
    if not (text.startswith("[") and text.endswith("]")):
        raise ValueError(f"expected inline list: {text!r}")
    inner = text[1:-1]
    result: list = []
    pos = 0
    n = len(inner)
    while pos < n:
        while pos < n and inner[pos] in " ,":
            pos += 1
        if pos >= n:
            break
        value, pos = _read_inline_value(inner, pos)
        result.append(value)
    return result


class _YamlMiniParser:
    """Indentation-aware parser for the goals.yaml subset described above."""

    _KEY_RE = re.compile(r"^([A-Za-z_][\w-]*)\s*:\s*(.*)$")

    def __init__(self, text: str) -> None:
        self.tokens: list[tuple[int, str]] = []
        for raw in text.splitlines():
            cleaned = _strip_inline_comment(raw)
            stripped_lhs = cleaned.lstrip()
            if not stripped_lhs or stripped_lhs.startswith("#"):
                continue
            indent = len(cleaned) - len(stripped_lhs)
            self.tokens.append((indent, stripped_lhs.rstrip()))
        self.pos = 0

    def _peek(self) -> tuple[int, str] | None:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def _parse_block_scalar(self, base_indent: int, marker: str) -> str:
        lines: list[str] = []
        while self._peek() is not None:
            ti, tc = self._peek()
            if ti <= base_indent:
                break
            self.pos += 1
            lines.append(tc)
        return _fold_block_scalar(lines, marker)

    def parse_block_mapping(self, indent: int) -> dict:
        result: dict = {}
        while self._peek() is not None:
            ti, tc = self._peek()
            if ti < indent or tc.startswith("- "):
                break
            if ti > indent:
                # Over-indented stray line — should have been consumed by recursion.
                self.pos += 1
                continue
            m = self._KEY_RE.match(tc)
            if not m:
                break
            self.pos += 1
            key = m.group(1)
            v_text = m.group(2).strip()
            if not v_text:
                result[key] = self._parse_value_below(indent + 2)
            elif _is_block_scalar_marker(v_text):
                result[key] = self._parse_block_scalar(indent, v_text)
            elif v_text.startswith("{"):
                result[key] = _parse_inline_mapping(v_text)
            elif v_text.startswith("["):
                result[key] = _parse_inline_list(v_text)
            else:
                result[key] = _coerce_scalar(v_text)
        return result

    def parse_block_list(self, indent: int) -> list:
        items: list = []
        while self._peek() is not None:
            ti, tc = self._peek()
            if ti != indent or not tc.startswith("- "):
                break
            self.pos += 1
            rest = tc[2:].lstrip()
            if rest.startswith("{"):
                items.append(_parse_inline_mapping(rest))
                continue
            m = self._KEY_RE.match(rest)
            if m:
                first_key = m.group(1)
                v_text = m.group(2).strip()
                if not v_text:
                    first_value = self._parse_value_below(indent + 4)
                elif _is_block_scalar_marker(v_text):
                    first_value = self._parse_block_scalar(indent + 2, v_text)
                elif v_text.startswith("{"):
                    first_value = _parse_inline_mapping(v_text)
                else:
                    first_value = _coerce_scalar(v_text)
                tail = self.parse_block_mapping(indent + 2)
                merged: dict = {first_key: first_value}
                merged.update(tail)
                items.append(merged)
                continue
            items.append(_coerce_scalar(rest))
        return items

    def _parse_value_below(self, expected_indent: int):
        peek = self._peek()
        if peek is None or peek[0] < expected_indent:
            return None
        ti, tc = peek
        if tc.startswith("- "):
            return self.parse_block_list(ti)
        if self._KEY_RE.match(tc):
            return self.parse_block_mapping(ti)
        # Defensive: skip and return None
        return None


def parse_goals_yaml(text: str) -> list[dict]:
    """Parse a constrained goals.yaml subset. Returns a list of goal dicts."""
    parser = _YamlMiniParser(text)
    while parser._peek() is not None:
        ti, tc = parser._peek()
        if ti == 0 and re.match(r"^goals\s*:\s*$", tc):
            parser.pos += 1
            break
        parser.pos += 1
    else:
        return []
    peek = parser._peek()
    if peek is None or not peek[1].startswith("- "):
        return []
    return parser.parse_block_list(peek[0])


def load_goals(path: Path) -> list[dict]:
    text = path.read_text(encoding="utf-8", errors="replace")
    return validate_goals(parse_goals_yaml(text), source_name=str(path))


def _raise_goals_validation(source_name: str, message: str) -> None:
    raise GoalsValidationError(f"{source_name}: {message}")


def _validate_nonempty_string(value, path: str, source_name: str) -> str:
    if not isinstance(value, str):
        _raise_goals_validation(source_name, f"{path} must be a non-empty string")
    text = value.strip()
    if not text:
        _raise_goals_validation(source_name, f"{path} must be a non-empty string")
    return text


def _validate_slug_like(value, path: str, source_name: str) -> str:
    if value is None or isinstance(value, bool):
        _raise_goals_validation(source_name, f"{path} must be a non-empty slug")
    text = str(value).strip()
    if not text:
        _raise_goals_validation(source_name, f"{path} must be a non-empty slug")
    return text


def _validate_anchor(anchor, path: str, source_name: str):
    if not isinstance(anchor, dict) or len(anchor) != 1:
        _raise_goals_validation(
            source_name,
            f"{path} must be a single-key mapping like {{ section: '2.1' }}",
        )
    key, value = next(iter(anchor.items()))
    key_text = _validate_nonempty_string(key, f"{path} key", source_name)
    if isinstance(value, (dict, list)):
        _raise_goals_validation(source_name, f"{path}.{key_text} must be a scalar")
    return {key_text: value}


def _validate_source_entry(source_entry, path: str, source_name: str) -> dict:
    if not isinstance(source_entry, dict):
        _raise_goals_validation(source_name, f"{path} must be a mapping")
    if "slug" not in source_entry:
        _raise_goals_validation(source_name, f"{path}.slug is required")
    normalized = dict(source_entry)
    normalized["slug"] = _validate_slug_like(source_entry.get("slug"), f"{path}.slug", source_name)
    if "anchor" in source_entry and source_entry.get("anchor") is not None:
        normalized["anchor"] = _validate_anchor(source_entry.get("anchor"), f"{path}.anchor", source_name)
    return normalized


def _validate_concept_entry(concept_entry, path: str, source_name: str):
    if isinstance(concept_entry, str):
        return _validate_nonempty_string(concept_entry, path, source_name)
    if not isinstance(concept_entry, dict):
        _raise_goals_validation(source_name, f"{path} must be a string or mapping")
    normalized = dict(concept_entry)
    normalized["name"] = _validate_nonempty_string(concept_entry.get("name"), f"{path}.name", source_name)
    sources = concept_entry.get("sources")
    if sources is None:
        return normalized
    if not isinstance(sources, list):
        _raise_goals_validation(source_name, f"{path}.sources must be a list")
    normalized["sources"] = [
        _validate_source_entry(source, f"{path}.sources[{idx}]", source_name)
        for idx, source in enumerate(sources)
    ]
    return normalized


def _validate_declarations(declarations, path: str, source_name: str) -> list[str]:
    if not isinstance(declarations, list):
        _raise_goals_validation(source_name, f"{path} must be a list")
    normalized: list[str] = []
    for idx, decl in enumerate(declarations):
        text = _validate_nonempty_string(decl, f"{path}[{idx}]", source_name)
        if not LEAN_DECL_NAME.match(text):
            _raise_goals_validation(
                source_name,
                f"{path}[{idx}] must be a dotted Lean declaration name",
            )
        normalized.append(text)
    return normalized


def validate_goals(goals, *, source_name: str = "goals.yaml") -> list[dict]:
    """Validate and normalize the parsed goals.yaml structure."""
    if not isinstance(goals, list) or not goals:
        _raise_goals_validation(
            source_name,
            "expected a non-empty top-level `goals:` list",
        )

    normalized_goals: list[dict] = []
    seen_ids: set[str] = set()
    for idx, goal in enumerate(goals):
        path = f"goals[{idx}]"
        if not isinstance(goal, dict):
            _raise_goals_validation(source_name, f"{path} must be a mapping")
        goal_id = _validate_nonempty_string(goal.get("id"), f"{path}.id", source_name)
        if goal_id in seen_ids:
            _raise_goals_validation(source_name, f"duplicate goal id: {goal_id}")
        seen_ids.add(goal_id)

        normalized = dict(goal)
        normalized["id"] = goal_id
        normalized["description"] = _validate_nonempty_string(
            goal.get("description"), f"{path}.description", source_name
        )
        normalized["declarations"] = _validate_declarations(
            goal.get("declarations"), f"{path}.declarations", source_name
        )

        concepts = goal.get("concepts")
        if concepts is None:
            normalized["concepts"] = []
        else:
            if not isinstance(concepts, list):
                _raise_goals_validation(source_name, f"{path}.concepts must be a list")
            normalized["concepts"] = [
                _validate_concept_entry(
                    concept,
                    f"{path}.concepts[{concept_idx}]",
                    source_name,
                )
                for concept_idx, concept in enumerate(concepts)
            ]
        normalized_goals.append(normalized)

    return normalized_goals


# --- Lean source scanner (used by `--lean-root`) ---------------------------

# Decl-keyword line. The optional prefix block matches the modifiers and
# attribute brackets that may legally precede the keyword. The trailing
# group captures the declaration's short name.
_LEAN_DECL_RE = re.compile(
    r"""
    ^\s*
    (?:(?:noncomputable|private|protected|partial|nonrec|unsafe|@\[[^\]]*\])\s+)*
    (theorem|lemma|def|structure|class|instance|inductive|abbrev|axiom|opaque)
    \s+
    (?:@\[[^\]]*\]\s*)*
    ([A-Za-z_][\w']*)
    """,
    re.VERBOSE,
)
_LEAN_NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w'.]*)\s*$")
_LEAN_SECTION_OPEN_RE = re.compile(r"^\s*section(?:\s+([A-Za-z_][\w']*))?\s*$")
_LEAN_END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w'.]*))?\s*$")


def scan_lean_declarations(lean_root: Path) -> set[str]:
    """Walk ``lean_root/**/*.lean`` and collect fully-qualified declaration
    names by tracking each file's ``namespace`` / ``end`` stack.

    Sections are tracked but do not contribute to the qualified prefix
    (Lean's behaviour). Anonymous declarations (``instance : ... := …``,
    ``example``) are skipped because they have no name to collect.
    """
    decls: set[str] = set()
    for path in sorted(lean_root.rglob("*.lean")):
        stack: list[tuple[str, str]] = []  # (kind, name)
        in_block_comment = False
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for line in text.splitlines():
            # Naive block comment handling — `/-` ... `-/` on different lines.
            if in_block_comment:
                idx = line.find("-/")
                if idx == -1:
                    continue
                line = line[idx + 2 :]
                in_block_comment = False
            while "/-" in line:
                start = line.find("/-")
                end = line.find("-/", start + 2)
                if end == -1:
                    line = line[:start]
                    in_block_comment = True
                    break
                line = line[:start] + line[end + 2 :]
            if "--" in line:
                line = line.split("--", 1)[0]
            if not line.strip():
                continue
            m_ns = _LEAN_NAMESPACE_OPEN_RE.match(line)
            if m_ns:
                stack.append(("namespace", m_ns.group(1)))
                continue
            m_sec = _LEAN_SECTION_OPEN_RE.match(line)
            if m_sec:
                stack.append(("section", m_sec.group(1) or ""))
                continue
            m_end = _LEAN_END_RE.match(line)
            if m_end and stack:
                stack.pop()
                continue
            m_d = _LEAN_DECL_RE.match(line)
            if m_d:
                name = m_d.group(2)
                prefix = ".".join(item[1] for item in stack if item[0] == "namespace")
                decls.add(f"{prefix}.{name}" if prefix else name)
    return decls


def collect_entries(references_root: Path) -> dict[str, list[dict]]:
    """Return ``{slug: [bullet_entry, ...]}`` for every ``<slug>/INDEX.md``."""
    result: dict[str, list[dict]] = {}
    for entry in sorted(references_root.iterdir()):
        if not entry.is_dir():
            continue
        index_path = entry / "INDEX.md"
        if not index_path.is_file():
            continue
        text = index_path.read_text(encoding="utf-8", errors="replace")
        slug = _read_frontmatter_slug(text, entry.name)
        result[slug] = parse_key_concepts(text)
    return result


def classify_across_slugs(
    all_entries: dict[str, list[dict]], target_slug: str | None
) -> dict:
    """Aggregate per-concept status across all slugs, scoped to target if given."""
    # concept_name → list of (slug, status, annotation)
    per_concept: dict[str, list[tuple[str, dict]]] = defaultdict(list)
    for slug, bullets in all_entries.items():
        for entry in bullets:
            per_concept[entry["name"]].append((slug, entry))

    formalized: list[dict] = []
    resolved: list[dict] = []
    partial: list[dict] = []
    suspect: list[dict] = []
    gaps: list[dict] = []
    ambiguous: list[dict] = []
    other_knowledge: list[dict] = []

    for name, occurrences in sorted(per_concept.items()):
        statuses = {status for _, e in occurrences for status in (e["status"],)}
        display = occurrences[0][1]["display"]
        sources = []
        best_mathlib = ""
        best_formalized = ""
        other_slugs: list[str] = []
        for slug, e in occurrences:
            sources.append({"slug": slug, "annotation": e["annotation"]})
            ann = e["annotation"]
            if "formalized:" in ann.lower() and not best_formalized:
                best_formalized = ann
            if "mathlib:" in ann and not best_mathlib:
                best_mathlib = ann
            if slug != target_slug:
                other_slugs.append(slug)
        if target_slug is not None:
            from_target = any(slug == target_slug for slug, _ in occurrences)
            if not from_target:
                other_status = _strongest_status(statuses)
                other_knowledge.append(
                    {
                        "concept": display,
                        "sources": sources,
                        "status": other_status,
                        "mathlib_annotation": best_mathlib,
                        "formalized_annotation": best_formalized,
                    }
                )
                continue
        record = {
            "concept": display,
            "sources": sources,
            "mathlib_annotation": best_mathlib,
            "formalized_annotation": best_formalized,
            "supplementary_slugs": other_slugs,
        }
        # Tier order: formalized > resolved > partial > suspect > gap > ambiguous.
        # ``formalized`` always wins because a local Lean proof is the
        # strongest evidence; a ``suspect`` mathlib annotation does not
        # demote it.
        if "formalized" in statuses:
            formalized.append(record)
        elif "suspect" in statuses and "resolved" not in statuses:
            # verify_mathlib_refs.py flagged this annotation as wrong and
            # no other slug provides a clean mathlib mapping.
            suspect.append(record)
        elif "resolved" in statuses:
            resolved.append(record)
        elif "gap" in statuses:
            if other_slugs:
                # Still gap per mathlib, but some non-target source also
                # documents it — treat as partially closed for prioritisation.
                partial.append(record)
            else:
                gaps.append(record)
        else:
            ambiguous.append(record)

    # coverage_score weights:
    #   formalized = 1.0   (locally proven — strongest evidence)
    #   resolved   = 1.0   (mathlib has it; trusted after verify_mathlib_refs)
    #   partial    = 0.5   (target says gap, but a sibling slug documents it)
    # target_total excludes other_knowledge (non-target slug concepts),
    # because gap-filler's goal is the target's own knowledge closure.
    target_total = (
        len(formalized) + len(resolved) + len(partial)
        + len(suspect) + len(gaps) + len(ambiguous)
    )
    coverage = 0.0
    if target_total:
        coverage = (
            len(formalized) * 1.0 + len(resolved) * 1.0 + len(partial) * 0.5
        ) / target_total
    return {
        "target_slug": target_slug,
        "formalized": formalized,
        "resolved": resolved,
        "partial": partial,
        "suspect": suspect,
        "gaps": gaps,
        "ambiguous": ambiguous,
        "other_knowledge": other_knowledge,
        "counts": {
            "formalized": len(formalized),
            "resolved": len(resolved),
            "partial": len(partial),
            "suspect": len(suspect),
            "gaps": len(gaps),
            "ambiguous": len(ambiguous),
            "other_knowledge": len(other_knowledge),
        },
        "coverage_score": round(coverage, 3),
        "coverage_breakdown": {
            "target_total": target_total,
            "formalized_weight": 1.0,
            "resolved_weight": 1.0,
            "partial_weight": 0.5,
            "formula": (
                "(formalized*1.0 + resolved*1.0 + partial*0.5) / "
                "(formalized + resolved + partial + suspect + gaps + ambiguous)"
            ),
        },
    }


def _all_concept_occurrences(
    all_entries: dict[str, list[dict]],
) -> dict[str, list[dict]]:
    """Return ``{normalised_name: [{slug, status, annotation, display}, ...]}``.

    Unlike a "best status per concept" view, this preserves every per-slug
    occurrence so the goal evaluator can filter by ``sources[*].slug``
    when a concept has been pinned to specific references.
    """
    out: dict[str, list[dict]] = defaultdict(list)
    for slug, bullets in all_entries.items():
        for entry in bullets:
            out[entry["name"]].append(
                {
                    "slug": slug,
                    "status": entry["status"],
                    "annotation": entry["annotation"],
                    "display": entry["display"],
                }
            )
    return out


def _best_status(occurrences: list[dict]) -> str:
    """Pick the strongest tier from a list of per-slug occurrence records."""
    statuses = {o["status"] for o in occurrences}
    if not statuses:
        return "unknown"
    return _strongest_status(statuses)


def _strongest_status(statuses: set[str]) -> str:
    """Pick the strongest concept tier from a set of statuses."""
    if "formalized" in statuses:
        return "formalized"
    if "resolved" in statuses:
        return "resolved"
    if "suspect" in statuses:
        return "suspect"
    if "gap" in statuses:
        return "gap"
    return "ambiguous"


def _evaluate_concept_entry(
    concept_entry,
    occurrences_map: dict[str, list[dict]],
) -> dict:
    """Resolve one ``concepts:`` list element against the references tree.

    ``concept_entry`` is either a bare string (any slug counts) or a
    ``{name, sources}`` mapping where each source pins the concept to a
    specific ``slug`` (and optionally a free-form ``anchor`` for human
    navigation). When ``sources`` is given, only matching slugs are
    consulted; if none of the wanted slugs document the concept, status
    is ``unknown``.
    """
    if isinstance(concept_entry, str):
        name = concept_entry
        sources_filter: list = []
    elif isinstance(concept_entry, dict):
        name = str(concept_entry.get("name") or "")
        sources_filter = concept_entry.get("sources") or []
    else:
        name = str(concept_entry)
        sources_filter = []

    normalised = _normalise_concept(name)
    occurrences = occurrences_map.get(normalised, [])

    if sources_filter:
        wanted = {
            str(s.get("slug"))
            for s in sources_filter
            if isinstance(s, dict) and s.get("slug") is not None
        }
        filtered = [o for o in occurrences if str(o["slug"]) in wanted]
    else:
        filtered = occurrences

    return {
        "name": name,
        "normalized": normalised,
        "status": _best_status(filtered),
        "sources_hint": sources_filter,
        "matched_sources": [
            {"slug": o["slug"], "annotation": o["annotation"]} for o in filtered
        ],
    }


def _verify_declarations(decls: list[str], lean_decls: set[str] | None) -> list[dict]:
    """Tag each declaration name with ``verified`` / ``missing`` / ``unverified``.

    ``unverified`` means the caller did not pass ``--lean-root``, so the
    Lean source could not be scanned; this is a soft state, distinct
    from "we looked and could not find it".
    """
    if lean_decls is None:
        return [{"name": d, "status": "unverified"} for d in decls]
    return [
        {"name": d, "status": "verified" if d in lean_decls else "missing"}
        for d in decls
    ]


def evaluate_goals(
    all_entries: dict[str, list[dict]],
    goals: list[dict],
    lean_decls: set[str] | None = None,
) -> dict:
    """Score each goal against the project's Lean source and references tree.

    A goal is satisfied when every name in its ``declarations`` list is
    present in the scanned Lean tree. ``concepts`` is *informational* —
    it indicates which prerequisite knowledge the goal depends on, so
    ``gap-filler`` can suggest what to ingest next, but it does not
    enter the satisfaction judgement. When ``lean_decls`` is ``None``
    (no ``--lean-root`` passed) every goal is reported as ``unverified``
    rather than guessed.

    Coverage formula: ``verified_declarations / total_declarations`` over
    every goal. Goals declared with an empty ``declarations: []`` (TODOs)
    contribute one missing slot to the denominator so they show up as
    incomplete.
    """
    occurrences_map = _all_concept_occurrences(all_entries)
    goal_records: list[dict] = []

    total_decls = 0
    verified_decls = 0

    sat = part = miss = unverified_count = 0

    for goal in goals:
        decls = goal.get("declarations") or []
        decl_results = _verify_declarations(decls, lean_decls)
        verified_in_goal = sum(1 for r in decl_results if r["status"] == "verified")
        missing_in_goal = sum(1 for r in decl_results if r["status"] == "missing")

        # Coverage accounting. Empty-declaration goals count as one missing
        # slot so untouched TODOs do not silently inflate the score.
        if not decls:
            total_decls += 1
        else:
            total_decls += len(decls)
            verified_decls += verified_in_goal

        # Goal-level status.
        if not decls:
            goal_status = "missing"
            miss += 1
        elif lean_decls is None:
            goal_status = "unverified"
            unverified_count += 1
        elif missing_in_goal == 0:
            goal_status = "satisfied"
            sat += 1
        elif verified_in_goal == 0:
            goal_status = "missing"
            miss += 1
        else:
            goal_status = "partially_satisfied"
            part += 1

        # Concept evaluation — informational only, used by gap-filler hints.
        concept_results = [
            _evaluate_concept_entry(c, occurrences_map)
            for c in (goal.get("concepts") or [])
        ]

        goal_records.append(
            {
                "id": goal.get("id"),
                "description": goal.get("description"),
                "declarations": decl_results,
                "concepts": concept_results,
                "missing_declarations": [
                    r["name"] for r in decl_results if r["status"] == "missing"
                ],
                "missing_concepts": [
                    c["name"]
                    for c in concept_results
                    if c["status"] in ("unknown", "ambiguous", "gap", "suspect")
                ],
                "goal_status": goal_status,
            }
        )

    coverage = (verified_decls / total_decls) if total_decls else 0.0

    return {
        "goals": goal_records,
        "goals_summary": {
            "total": len(goals),
            "satisfied": sat,
            "partially_satisfied": part,
            "missing": miss,
            "unverified": unverified_count,
            "declarations_total": total_decls,
            "declarations_verified": verified_decls,
            "goal_coverage_score": round(coverage, 3),
            "formula": "verified_declarations / total_declarations",
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("references_root", help="Directory that contains per-slug subdirs")
    parser.add_argument("--target-slug", default=None, help="Slug whose gaps we care about")
    parser.add_argument(
        "--goals",
        default=None,
        help=(
            "Path to a goals.yaml that lists the formalization targets. "
            "When given, the report adds a per-goal status block. Goal "
            "satisfaction is decided by `declarations` (verified against "
            "the Lean tree at --lean-root); `concepts` is informational."
        ),
    )
    parser.add_argument(
        "--lean-root",
        default=None,
        help=(
            "Path to the Lean source tree (e.g. ./QuantumSystem). Each "
            "goal's `declarations` is checked against the set of "
            "fully-qualified theorem/def/structure/class/instance names "
            "found by walking <lean-root>/**/*.lean. Without this flag, "
            "declarations are reported as `unverified`."
        ),
    )
    parser.add_argument("--output", default=None, help="Write JSON here; default: stdout")
    parser.add_argument(
        "--history-log",
        default=None,
        help=(
            "Append a one-line JSON record per run to this path. Default: "
            "<references-root>/gaps-history.jsonl (skipped only when "
            "--no-history is also passed)."
        ),
    )
    parser.add_argument(
        "--no-history",
        action="store_true",
        help="Suppress the append-only history log entirely.",
    )
    args = parser.parse_args()

    root = Path(args.references_root).expanduser().resolve()
    if not root.is_dir():
        print(f"[error] not a directory: {root}", file=sys.stderr)
        return 2

    all_entries = collect_entries(root)
    report = classify_across_slugs(all_entries, args.target_slug)

    # Surface the live issue count so the user sees outstanding items
    # (false-positive mathlib refs, skipped notation candidates, …)
    # alongside the concept-tier breakdown.
    issues_dir = root / "issues"
    if issues_dir.is_dir():
        report["issues"] = {
            "open": sum(
                1
                for entry in issues_dir.iterdir()
                if entry.is_file() and entry.suffix == ".yaml"
            ),
            "directory": str(issues_dir),
        }
    else:
        report["issues"] = {"open": 0, "directory": str(issues_dir)}

    lean_decls: set[str] | None = None
    if args.lean_root:
        lean_root = Path(args.lean_root).expanduser().resolve()
        if not lean_root.is_dir():
            print(f"[error] not a directory: {lean_root}", file=sys.stderr)
            return 2
        lean_decls = scan_lean_declarations(lean_root)
        report["lean_root"] = str(lean_root)
        report["lean_declarations_count"] = len(lean_decls)

    if args.goals:
        goals_path = Path(args.goals).expanduser().resolve()
        if not goals_path.is_file():
            print(f"[error] goals file not found: {goals_path}", file=sys.stderr)
            return 2
        try:
            goals = load_goals(goals_path)
        except GoalsValidationError as exc:
            print(f"[error] invalid goals file: {exc}", file=sys.stderr)
            return 2
        report["goals_file"] = str(goals_path)
        report.update(evaluate_goals(all_entries, goals, lean_decls))

    if not args.no_history:
        history_path = (
            Path(args.history_log).expanduser().resolve()
            if args.history_log
            else root / "gaps-history.jsonl"
        )
        record: dict = {
            "timestamp": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
            "target_slug": args.target_slug,
            "coverage_score": report["coverage_score"],
            "counts": report["counts"],
            "issues_open": report["issues"]["open"],
        }
        if args.goals:
            gs = report["goals_summary"]
            record["goals"] = {
                "total": gs["total"],
                "satisfied": gs["satisfied"],
                "partially_satisfied": gs["partially_satisfied"],
                "missing": gs["missing"],
                "unverified": gs.get("unverified", 0),
                "declarations_total": gs.get("declarations_total", 0),
                "declarations_verified": gs.get("declarations_verified", 0),
                "goal_coverage_score": gs["goal_coverage_score"],
            }
        history_path.parent.mkdir(parents=True, exist_ok=True)
        with history_path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(record, ensure_ascii=False) + "\n")
        report["history_log"] = str(history_path)

    payload = json.dumps(report, indent=2, ensure_ascii=False)
    if args.output:
        Path(args.output).write_text(payload + "\n", encoding="utf-8")
        summary_msg = f"[ok] wrote {args.output}: {report['counts']}"
        if report["issues"]["open"]:
            summary_msg += f" | open issues: {report['issues']['open']}"
        if args.goals:
            gs = report["goals_summary"]
            summary_msg += (
                f" | goals: {gs['satisfied']}/{gs['total']} satisfied, "
                f"goal_coverage_score={gs['goal_coverage_score']}"
            )
        print(summary_msg, file=sys.stderr)
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
