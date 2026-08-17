// Ground truth for the render check: run an extraction note through the same
// markdown + KaTeX pipeline a previewer uses, and report every ParseError with
// the note's own line number.
//
// Why a real markdown pipeline and not a hand-rolled `$…$` scanner: the scanner
// version of this script reported "0 ParseErrors" on a note that threw two of
// them in VS Code. A markdown renderer decides what a math span *is* — where it
// starts, where it ends, whether a `$` is math at all — and it does not agree
// with a regex. Delimiter pairing across lines, `$` inside table cells, and
// emphasis interacting with `^*` are all places the two diverge. So the check
// renders the document.
//
// Two facts worth keeping in view while reading a failure:
//
//   * KaTeX's \newcommand is a *local* definition. It does not survive from one
//     math span to the next -- not even when the renderer passes a shared
//     `macros` object -- so a `$$`-block preamble of \newcommands leaves every
//     later use throwing `Undefined control sequence`. Only \gdef is written
//     back, and only a renderer that shares macro state carries it.
//   * A command can be perfectly well defined and still fail: `\widetilde\mathcal U`
//     and `\Delta_\mathcal U` are parse errors because `\widetilde` and `_` take a
//     single token. No allowlist catches that; a parser does.
//
//   node render_check.js <note.md>
//
// Reported in two classes:
//
//   ParseError         the pipeline could not typeset the span at all.
//   portability hazard the span typesets *here* but relies on behaviour engines
//                      disagree about — `\,_2` (a subscripted thin space) and
//                      `\Delta_\mathcal U` (an unbraced multi-token argument)
//                      are the two that reached a reader before this check
//                      existed. KaTeX 0.16.47 and 0.18.4 both accept them.
//
// Requires markdown-it and @vscode/markdown-it-katex, which is the plugin VS
// Code's own Markdown preview uses:
//
//   (cd .claude/skills/math-extract && npm install --no-save markdown-it @vscode/markdown-it-katex)
//
// Exit 0 clean, 1 on findings, 2 if the pipeline is unavailable.

const fs = require('fs');

let MarkdownIt, katexPlugin, katex;
try {
  MarkdownIt = require('markdown-it');
  katex = require('@vscode/markdown-it-katex/node_modules/katex');
  katexPlugin = require('@vscode/markdown-it-katex').default
    || require('@vscode/markdown-it-katex');
} catch (e) {
  console.error('pipeline unavailable: ' + e.message);
  process.exit(2);
}

const file = process.argv[2];
if (!file) { console.error('usage: node render_check.js <note.md>'); process.exit(2); }
const text = fs.readFileSync(file, 'utf8');

const errors = [];
const md = new MarkdownIt({ html: true })
  .use(katexPlugin, {
    throwOnError: true,
    strict: false,
    // The plugin swallows the error and emits it as HTML; capture it instead.
    errorColor: '#cc0000',
  });

// The plugin catches KaTeX errors internally and renders them as text, so hook
// the renderer rules to see them rather than trusting an exception to escape.
for (const rule of ['math_inline', 'math_block', 'math_inline_block', 'math_block_eqno']) {
  const prev = md.renderer.rules[rule];
  if (!prev) continue;
  md.renderer.rules[rule] = function (tokens, idx, options, env, self) {
    const out = prev.call(this, tokens, idx, options, env, self);
    if (/katex-error|ParseError|Undefined control sequence/i.test(out)) {
      const tok = tokens[idx];
      const line = tok.map ? tok.map[0] + 1 : null;
      // Re-run the span through KaTeX directly to recover the message text; the
      // plugin only leaves a coloured placeholder in the HTML.
      let why = 'KaTeX error';
      try {
        katex.renderToString(tok.content, { throwOnError: true, strict: false });
      } catch (err) {
        why = (err.rawMessage || err.message || why).split('\n')[0];
      }
      errors.push({ line, tex: tok.content, why });
    }
    return out;
  };
}

// Portability hazards: constructs that *this* KaTeX build happens to accept but
// that other engines reject. They are the ones that get reported by a reader
// rather than by the check, so they are collected from the spans the pipeline
// actually extracted -- inline code and fenced blocks are excluded for free.
const hazards = [];
const HAZARD_RULES = [
  [/\\[,;:!]\s*[_^]|\\q?quad\s*[_^]/,
   'a spacing command (\\, \\; \\: \\! \\quad) immediately subscripted or superscripted — '
   + 'subscripting a space is meaningless and engines disagree on whether it is an error'],
  [/(?:[_^]|\\widetilde|\\overline|\\bar|\\hat|\\tilde|\\vec)\s*\\(?:mathcal|mathrm|mathbb|mathfrak|operatorname)\b/,
   'an unbraced multi-token argument (e.g. \\widetilde\\mathcal U) — brace it: \\widetilde{\\mathcal U}'],
];
for (const rule of ['math_inline', 'math_block', 'math_inline_block', 'math_block_eqno']) {
  const prev = md.renderer.rules[rule];
  if (!prev) continue;
  const wrapped = md.renderer.rules[rule];
  md.renderer.rules[rule] = function (tokens, idx, options, env, self) {
    const tex = tokens[idx].content;
    for (const [re, why] of HAZARD_RULES) if (re.test(tex)) hazards.push({ tex, why });
    return wrapped.call(this, tokens, idx, options, env, self);
  };
}

// The plugin dumps each KaTeX error object through `console.log` as it goes.
// We report the same errors ourselves, with line numbers, so silence it for the
// duration of the render only.
const realLog = console.log;
console.log = () => {};
try {
  md.render(text);
} finally {
  console.log = realLog;
}

// The token map is only reliable for block tokens; recover inline line numbers
// by locating the offending TeX in the source.
const lines = text.split('\n');
function locate(tex) {
  const needle = tex.trim().split('\n')[0].trim();
  if (!needle) return null;
  for (let i = 0; i < lines.length; i++) if (lines[i].includes(needle)) return i + 1;
  return null;
}

for (const e of errors) {
  const line = locate(e.tex) || e.line || '?';
  console.log(`line ${line}: ${e.why.slice(0, 160)}`);
  console.log(`    ${e.tex.replace(/\s+/g, ' ').slice(0, 130)}`);
}

for (const h of hazards) {
  const line = locate(h.tex) || '?';
  console.log(`line ${line}: portability hazard — ${h.why}`);
  console.log(`    ${h.tex.replace(/\s+/g, ' ').slice(0, 130)}`);
}

console.log(
  `\n${errors.length} ParseError(s) and ${hazards.length} portability hazard(s) `
  + `from the markdown+KaTeX pipeline`
);
process.exit(errors.length + hazards.length ? 1 : 0);
