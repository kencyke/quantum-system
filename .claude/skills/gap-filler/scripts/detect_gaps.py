#!/usr/bin/env python3
# /// script
# requires-python = ">=3.10"
# dependencies = []
# ///
"""Scan a ``references/`` tree and report which Key concepts are still gaps.

A concept is classified by looking at the annotation on its Key concepts
bullet across every ``<slug>/INDEX.md`` under the root:

- ``→ mathlib: Mathlib.X.y`` → **resolved** (mathlib already has it).
- ``→ needs formalization`` → **gap** (no mathlib coverage).
- No annotation → **ambiguous** (treat as potential gap).

Concepts with the same normalised name coming from multiple sources are
merged; the aggregate classification is "resolved" if any source says so,
otherwise "gap" unless every annotation is "ambiguous".

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
NEEDS_FORMAL_ANNOT = re.compile(r"→\s*needs\s*formalization", re.IGNORECASE)
UNVERIFIED_MARKER = re.compile(r"\[UNVERIFIED\]", re.IGNORECASE)


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
        if MATHLIB_ANNOT.search(annotation) and UNVERIFIED_MARKER.search(annotation):
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
        best_annotation = ""
        other_slugs: list[str] = []
        for slug, e in occurrences:
            sources.append({"slug": slug, "annotation": e["annotation"]})
            if "mathlib:" in e["annotation"] and not best_annotation:
                best_annotation = e["annotation"]
            if slug != target_slug:
                other_slugs.append(slug)
        if target_slug is not None:
            from_target = any(slug == target_slug for slug, _ in occurrences)
            if not from_target:
                other_knowledge.append(
                    {
                        "concept": display,
                        "sources": sources,
                        "status": "resolved" if "resolved" in statuses else ("gap" if "gap" in statuses else "ambiguous"),
                        "mathlib_annotation": best_annotation,
                    }
                )
                continue
        record = {
            "concept": display,
            "sources": sources,
            "mathlib_annotation": best_annotation,
            "supplementary_slugs": other_slugs,
        }
        if "suspect" in statuses and "resolved" not in statuses:
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

    # coverage_score: (resolved*1.0 + partial*0.5) / target_total.
    # target_total excludes other_knowledge (non-target slug concepts),
    # because gap-filler's goal is the target's own knowledge closure.
    target_total = len(resolved) + len(partial) + len(suspect) + len(gaps) + len(ambiguous)
    coverage = 0.0
    if target_total:
        coverage = (len(resolved) * 1.0 + len(partial) * 0.5) / target_total
    return {
        "target_slug": target_slug,
        "resolved": resolved,
        "partial": partial,
        "suspect": suspect,
        "gaps": gaps,
        "ambiguous": ambiguous,
        "other_knowledge": other_knowledge,
        "counts": {
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
            "resolved_weight": 1.0,
            "partial_weight": 0.5,
            "formula": "(resolved*1.0 + partial*0.5) / (resolved + partial + suspect + gaps + ambiguous)",
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("references_root", help="Directory that contains per-slug subdirs")
    parser.add_argument("--target-slug", default=None, help="Slug whose gaps we care about")
    parser.add_argument("--output", default=None, help="Write JSON here; default: stdout")
    args = parser.parse_args()

    root = Path(args.references_root).expanduser().resolve()
    if not root.is_dir():
        print(f"[error] not a directory: {root}", file=sys.stderr)
        return 2

    all_entries = collect_entries(root)
    report = classify_across_slugs(all_entries, args.target_slug)

    payload = json.dumps(report, indent=2, ensure_ascii=False)
    if args.output:
        Path(args.output).write_text(payload + "\n", encoding="utf-8")
        print(f"[ok] wrote {args.output}: {report['counts']}", file=sys.stderr)
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
