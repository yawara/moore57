#!/usr/bin/env python3
"""Generate paper-formalization status pages under docs/papers/ from
the Lean sources in Moore57/Papers/.

Usage:
    python3 bin/gen_papers_status.py           # rewrite docs/papers/*.html
                                              # and the sentinel-marked
                                              # block in docs/index.html
    python3 bin/gen_papers_status.py --check   # exit 1 if regeneration
                                              # would change any file

The script is stdlib-only and produces deterministic output (sorted
sections, deterministic ordering of statements by source-line).
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from html import escape
from pathlib import Path
from typing import Optional

ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = ROOT / "Moore57" / "Papers"
DOCS_DIR = ROOT / "docs"
PAPERS_OUT = DOCS_DIR / "papers"
INDEX_PATH = DOCS_DIR / "index.html"

GITHUB_BLOB = "https://github.com/yawara/moore57/blob/main"

# Per-paper metadata. `section_order` controls the sort key + human label
# for the section grouping. Keys are either subdirectory names (used by
# MacajSiran2010) or file basenames without `.lean` (used by Cameron Ch3
# and the flat papers).
PAPERS: list[dict] = [
    {
        "key": "MacajSiran2010",
        "short": "Mačaj–Širáň 2010",
        "title": "Search for properties of the missing Moore graph",
        "venue": "Linear Algebra Appl. 432 (2010), 2381–2398",
        "doi": "10.1016/j.laa.2009.07.018",
        "section_via": "subdir",
        "section_order": [
            ("Citation",                         "Citation"),
            ("Section02_StateOfTheArt",          "§2 State of the art"),
            ("Section03_EquitablePartitions",    "§3 Equitable partitions"),
            ("Section04_Characters",             "§4 Characters"),
            ("Section05_Tables",                 "§5 Tables"),
            ("Section06_PGroupsOverview",        "§6 p-groups (overview)"),
            ("Section07_Theorem4Proof",          "§7 Theorem 4 proof"),
            ("Section08_Theorem5Proof",          "§8 Theorem 5 proof"),
            ("Section09_MixingPrimes",           "§9 Mixing primes"),
            ("MainTheorem",                      "Main theorem"),
        ],
    },
    {
        "key": "Aschbacher1971",
        "short": "Aschbacher 1971",
        "title": "The Nonexistence of Rank Three Permutation Groups of Degree 3250 and Subdegree 57",
        "venue": "J. Algebra 19 (1971), 538–540",
        "doi": "10.1016/0021-8693(71)90087-1",
        "section_via": "file",
        "section_order": [
            ("Citation",                       "Citation"),
            ("Lemma1_1_RegularOrStar",         "Lemma 1.1 — regular or star"),
            ("Lemma1_2_FixInheritsStar",       "Lemma 1.2 — fix inherits star"),
            ("Lemma1_3_ValenceClassification", "Lemma 1.3 — valence classification"),
            ("Lemma1_4_InvolutionFix",         "Lemma 1.4 — involution fix"),
            ("MainTheorem",                    "Main theorem"),
        ],
    },
    {
        "key": "Higman1964",
        "short": "Higman 1964",
        "title": "Finite permutation groups of rank 3",
        "venue": "Math. Zeitschr. 86 (1964), 145–156",
        "doi": "10.1007/BF01111335",
        "section_via": "file",
        "section_order": [
            ("Citation",                  "Citation"),
            ("Lemma01_PairedOrbits",      "§1 Lemma 1 — paired orbits"),
            ("Lemma02_IntersectionNumbers","§2 Lemma 2 — intersection numbers"),
            ("Lemma03_SelfPaired",        "§2 Lemma 3 — self-paired"),
            ("Lemma04_Imprimitivity",     "§2 Lemma 4 — imprimitivity"),
            ("Lemma05_BlockDesignCount",  "§3 Lemma 5 — block-design count"),
            ("Lemma06_TwoEigenvalues",    "§4 Lemma 6 — two eigenvalues"),
            ("Lemma07_IntegralityCases",  "§5 Lemma 7 — integrality cases"),
            ("Theorem1_DegreeKSqPlus1",   "§6 Theorem 1 — degree k²+1"),
            ("MainTheorem",               "Main theorem"),
        ],
    },
    {
        "key": "CameronCh3",
        "short": "Cameron, Permutation Groups, Ch. 3",
        "title": "Permutation Groups, Chapter 3 (Coherent configurations)",
        "venue": "Cambridge University Press, 1999",
        "doi": "10.1017/CBO9780511623677.004",
        "section_via": "file",
        "section_order": [
            ("Citation",                        "Citation"),
            ("Section01_Introduction",          "§3.1 Introduction"),
            ("Section02_AlgebraicTheory",       "§3.2 Algebraic theory"),
            ("Section03_AssociationSchemes",    "§3.3 Association schemes"),
            ("Section04_AlgebraOfSchemes",      "§3.4 Algebra of schemes"),
            ("Section05_StronglyRegularGraphs", "§3.5 Strongly regular graphs"),
            ("Section06_HoffmanSingleton",      "§3.6 Hoffman–Singleton graph"),
            ("Section07_Automorphisms",         "§3.7 Automorphisms"),
            ("Section08_ValencyBounds",         "§3.8 Valency bounds"),
            ("Section09_DistanceTransitive",    "§3.9 Distance-transitive graphs"),
            ("Section10_MultiplicityBounds",    "§3.10 Multiplicity bounds"),
            ("Section11_Duality",               "§3.11 Duality"),
            ("Section12_Wielandt",              "§3.12 Wielandt's theorem"),
            ("MainTheorem",                     "Main theorem"),
        ],
    },
    {
        "key": "MakhnevPaduchikh2001",
        "short": "Makhnev–Paduchikh 2001",
        "title": "Automorphisms of Aschbacher Graphs",
        "venue": "Algebra and Logic 40 (2) (2001), 69–74",
        "doi": "10.1023/A:1010217919915",
        "section_via": "file",
        "section_order": [
            ("Citation",                  "Citation"),
            ("Lemma01_StrongFix",         "Lemma 1 — strong fix"),
            ("Lemma02_InvolutionFix",     "Lemma 2 — involution fix"),
            ("Lemma03_OddPrimeFix",       "Lemma 3 — odd-prime fix"),
            ("Lemma04_InvolutionGood",    "Lemma 4 — involution good"),
            ("Lemmas05_to_09_Structure",  "Lemmas 5–9 — involution structure"),
            ("MainTheorem",               "Main theorem"),
        ],
    },
]

# Status taxonomy ----------------------------------------------------------

# Marker → primary status group.
MARKER_TO_STATUS: dict[str, str] = {
    "done":            "formalized",
    "wrap":            "formalized",
    "external":        "formalized",
    "skeleton":        "pending",
    "deferred-heavy":  "pending",
    "GAP":             "pending",
    "out-of-scope":    "out_of_scope",
}

# Status group → (badge CSS class, human label).
STATUS_BADGE: dict[str, tuple[str, str]] = {
    "formalized":   ("done",  "Formalized"),
    "pending":      ("open",  "Pending"),
    "out_of_scope": ("muted", "Out of scope"),
}

# Sub-tag → human label shown after the badge (small, muted).
SUBTAG_LABEL: dict[str, str] = {
    "done":             "done",
    "wrap":             "wrap",
    "external":         "external",
    "skeleton":         "skeleton",
    "deferred-heavy":   "deferred",
    "GAP":              "GAP-computation",
    "out-of-scope":     "out of scope",
    "auto-formalized":  "auto",
    "auto-pending":     "sorry",
    "auto-stub":        "stub",
}

# Regexes ------------------------------------------------------------------

DECL_RE = re.compile(
    r"^(?P<indent>\s*)(?:noncomputable\s+)?(?P<kw>theorem|lemma|def|structure)\s+(?P<name>\w+)",
    re.MULTILINE,
)
MARKER_RE = re.compile(
    r"\[(done|wrap|external|skeleton|deferred-heavy|GAP|out-of-scope)\]"
)
DOCSTRING_RE = re.compile(r"/--((?:.|\n)*?)-/")
MODULE_DOC_RE = re.compile(r"/-!((?:.|\n)*?)-/")
BOLD_RE = re.compile(r"\*\*([^*]+)\*\*")
PAPER_CLAIM_PREFIX_RE = re.compile(
    r"^(Lemma|Theorem|Proposition|Corollary|Main|Definition|Cor\.|Prop\.|Lem\.|Thm\.|Step\s+\d)",
    re.IGNORECASE,
)
TRIVIAL_BODY_RE = re.compile(r":\s*True\s*:=\s*by\s+trivial")


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass
class Statement:
    name: str
    line: int
    kind: str                  # 'theorem' | 'lemma' | 'def' | 'structure'
    title: str                 # bold-prefix of docstring, e.g. "Lemma 5 (1)"
    summary: str               # remainder after the prefix
    marker: Optional[str]
    status: str                # formalized | pending | out_of_scope
    subtag: str                # marker name, or auto-* tag
    has_sorry: bool
    is_trivial_stub: bool      # `: True := by trivial`


@dataclass
class FileInfo:
    paper: str
    rel_path: Path             # relative to repo root
    section_key: str           # subdir name or file basename
    section_label: str
    file_title: str            # from `/-! # ... -/`
    statements: list[Statement] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------


def _extract_module_title(text: str) -> str:
    m = MODULE_DOC_RE.search(text)
    if not m:
        return ""
    for ln in m.group(1).splitlines():
        s = ln.strip()
        if s.startswith("# "):
            return s[2:].strip()
    return ""


def _preceding_docstring(text: str, decl_start: int) -> Optional[str]:
    """Return the body of the `/-- ... -/` block that ends immediately before
    `decl_start` (only whitespace allowed between). None if absent."""
    before = text[:decl_start]
    blocks = list(DOCSTRING_RE.finditer(before))
    if not blocks:
        return None
    last = blocks[-1]
    between = before[last.end():]
    if between.strip():
        return None
    return last.group(1).strip()


def _decl_body(text: str, decl_start: int, next_decl_start: Optional[int]) -> str:
    end = next_decl_start if next_decl_start is not None else len(text)
    return text[decl_start:end]


def classify(marker: Optional[str], has_sorry: bool, is_trivial_stub: bool) -> tuple[str, str]:
    """Return (status_group, subtag)."""
    if marker is not None:
        return MARKER_TO_STATUS[marker], marker
    if has_sorry:
        return "pending", "auto-pending"
    if is_trivial_stub:
        # No marker, yet body is just `:= by trivial` returning True. Treat
        # as a placeholder (pending) rather than as a real proof.
        return "pending", "auto-stub"
    return "formalized", "auto-formalized"


def parse_lean_file(path: Path) -> tuple[str, list[Statement]]:
    text = path.read_text(encoding="utf-8")
    title = _extract_module_title(text)

    decls = list(DECL_RE.finditer(text))
    statements: list[Statement] = []
    for i, m in enumerate(decls):
        name = m.group("name")
        kind = m.group("kw")
        next_start = decls[i + 1].start() if i + 1 < len(decls) else None
        docstring = _preceding_docstring(text, m.start())
        if docstring is None:
            continue  # not a paper-tied declaration
        bold = BOLD_RE.search(docstring)
        if not bold:
            continue
        bold_content = bold.group(1).strip()
        marker_m = MARKER_RE.search(docstring)
        marker = marker_m.group(1) if marker_m else None
        # Accept as a paper-tied statement if it has an explicit status
        # marker, OR if its bold prefix names a paper-claim kind (Lemma /
        # Theorem / Proposition / Corollary / Main / Definition). The
        # marker check is what catches non-standard headings like
        # "Hoffman–Singleton graph" or Cameron's "Step N".
        if marker is None and not PAPER_CLAIM_PREFIX_RE.match(bold_content):
            continue
        if "helper" in bold_content.lower():
            continue
        body = _decl_body(text, m.start(), next_start)
        has_sorry = re.search(r"\bsorry\b", body) is not None
        is_trivial_stub = TRIVIAL_BODY_RE.search(body) is not None
        status, subtag = classify(marker, has_sorry, is_trivial_stub)
        # Build a one-line summary: text after the first `**...**` block,
        # stripping the marker and trimming to ~140 chars.
        rest = docstring[bold.end():].strip()
        rest = MARKER_RE.sub("", rest).strip(" .")
        # Drop common leading punctuation/quote chars.
        rest = rest.lstrip("`.,:; \t-").strip()
        # Collapse whitespace.
        rest = re.sub(r"\s+", " ", rest)
        if len(rest) > 220:
            rest = rest[:217].rstrip() + "…"
        line = text.count("\n", 0, m.start()) + 1
        statements.append(Statement(
            name=name, line=line, kind=kind,
            title=bold_content, summary=rest,
            marker=marker, status=status, subtag=subtag,
            has_sorry=has_sorry, is_trivial_stub=is_trivial_stub,
        ))
    return title, statements


def collect() -> dict[str, list[FileInfo]]:
    """Return {paper_key: [FileInfo...]} in section order, statements
    sorted by source line."""
    result: dict[str, list[FileInfo]] = {p["key"]: [] for p in PAPERS}

    for paper in PAPERS:
        key = paper["key"]
        paper_root = PAPERS_DIR / key
        section_keys_ordered = [s[0] for s in paper["section_order"]]
        section_label = {s[0]: s[1] for s in paper["section_order"]}
        section_via = paper["section_via"]
        # Bucket files by section key.
        bucket: dict[str, list[Path]] = defaultdict(list)
        for lean in sorted(paper_root.rglob("*.lean")):
            if section_via == "subdir":
                rel = lean.relative_to(paper_root)
                # If lean lives directly in paper_root, section key is its stem.
                if len(rel.parts) == 1:
                    section = rel.stem
                else:
                    section = rel.parts[0]
            else:  # 'file'
                rel = lean.relative_to(paper_root)
                section = rel.stem
            bucket[section].append(lean)

        # Emit in declared section order; warn about unknown sections.
        for section_key in section_keys_ordered:
            files = bucket.get(section_key, [])
            for lean in files:
                title, statements = parse_lean_file(lean)
                rel_repo = lean.relative_to(ROOT)
                result[key].append(FileInfo(
                    paper=key, rel_path=rel_repo,
                    section_key=section_key,
                    section_label=section_label[section_key],
                    file_title=title,
                    statements=statements,
                ))
        # Catch sections we forgot in the config.
        unknown = set(bucket) - set(section_keys_ordered)
        for section in sorted(unknown):
            for lean in bucket[section]:
                title, statements = parse_lean_file(lean)
                rel_repo = lean.relative_to(ROOT)
                result[key].append(FileInfo(
                    paper=key, rel_path=rel_repo,
                    section_key=section,
                    section_label=f"(unconfigured: {section})",
                    file_title=title, statements=statements,
                ))
    return result


# ---------------------------------------------------------------------------
# Aggregation
# ---------------------------------------------------------------------------


def aggregate(files: list[FileInfo]) -> dict[str, int]:
    counts = {"formalized": 0, "pending": 0, "out_of_scope": 0, "total": 0}
    for f in files:
        for s in f.statements:
            counts[s.status] += 1
            counts["total"] += 1
    return counts


def progress_bar(counts: dict[str, int]) -> str:
    total = max(counts["total"], 1)
    f_pct = counts["formalized"] / total * 100
    p_pct = counts["pending"] / total * 100
    o_pct = counts["out_of_scope"] / total * 100
    return (
        '<div class="progress" role="img" aria-label="'
        f'{counts["formalized"]} formalized, {counts["pending"]} pending, '
        f'{counts["out_of_scope"]} out of scope">'
        f'<span class="seg done"  style="width:{f_pct:.2f}%"></span>'
        f'<span class="seg open"  style="width:{p_pct:.2f}%"></span>'
        f'<span class="seg muted" style="width:{o_pct:.2f}%"></span>'
        '</div>'
    )


def progress_caption(counts: dict[str, int]) -> str:
    total = counts["total"]
    if total == 0:
        return '<span class="muted">no paper-tied statements</span>'
    return (
        f'<span class="muted">'
        f'<span class="dot done"></span>{counts["formalized"]} formalized · '
        f'<span class="dot open"></span>{counts["pending"]} pending · '
        f'<span class="dot muted"></span>{counts["out_of_scope"]} out of scope · '
        f'total {total}'
        f'</span>'
    )


# ---------------------------------------------------------------------------
# HTML emission
# ---------------------------------------------------------------------------

SITE_HEAD_TMPL = """<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title}</title>
<meta name="description" content="{description}">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@picocss/pico@2/css/pico.min.css">
<link rel="stylesheet" href="{css_href}">
</head>
<body>
<main class="container">

<header class="site">
  <hgroup>
    <h1>{h1}</h1>
    <p class="sub">{sub}</p>
  </hgroup>
  <nav>
    <ul>
      <li><a href="{nav_top}">Top</a></li>
      <li><a href="{nav_papers}">Papers</a></li>
      <li><a href="{nav_about}">About</a></li>
      <li><a href="{nav_contribute}">Contribute</a></li>
      <li><a href="https://github.com/yawara/moore57">GitHub</a></li>
    </ul>
  </nav>
</header>
"""

SITE_FOOT = """<footer class="site">
  Source &amp; Lean proofs: <a href="https://github.com/yawara/moore57">github.com/yawara/moore57</a>.
  Maintained by Yawara Ishida.
</footer>

</main>
</body>
</html>
"""

GEN_NOTICE = (
    "<!-- AUTO-GENERATED by bin/gen_papers_status.py from "
    "Moore57/Papers/**.lean. Do not edit by hand. -->\n"
)


def site_head(*, title: str, description: str, h1: str, sub: str,
              level: int) -> str:
    """level=0 for docs/papers/index.html, 1 for docs/papers/<paper>.html."""
    prefix = "../" if level == 1 else ""
    css = "../style.css" if level >= 0 else "style.css"
    css = ("../" if level == 1 else "") + "style.css"
    return SITE_HEAD_TMPL.format(
        title=title, description=description, h1=h1, sub=sub,
        css_href=css,
        nav_top=("../" if level == 1 else "") + "index.html",
        nav_papers=("../" if level == 1 else "") + "papers/index.html",
        nav_about=("../" if level == 1 else "") + "about.html",
        nav_contribute=("../" if level == 1 else "") + "contribute.html",
    )


def render_papers_index(per_paper: dict[str, list[FileInfo]]) -> str:
    head = site_head(
        title="Paper formalization status — Moore (57, 2) graph",
        description=(
            "Status of Lean 4 / Mathlib formalization for the 5 reference "
            "papers underpinning the Moore57 project."
        ),
        h1="Paper formalization status",
        sub=(
            "Lean 4 / Mathlib formalization of the 5 reference papers "
            "underpinning the Moore (57, 2) automorphism bounds. Per-paper "
            "progress at a glance; click through for §-level detail."
        ),
        level=1,
    )

    # Aggregate over all papers.
    overall = {"formalized": 0, "pending": 0, "out_of_scope": 0, "total": 0}
    for files in per_paper.values():
        c = aggregate(files)
        for k in overall:
            overall[k] += c[k]

    body_parts = [GEN_NOTICE, head]
    body_parts.append(
        '<section>\n'
        '<p>Each paper below mirrors one source reference under '
        '<code>Moore57/Papers/&lt;paper&gt;/</code>. Statements marked '
        '<span class="badge done">Formalized</span> have a Lean proof '
        '(explicit <code>[done]/[wrap]/[external]</code> marker, or a '
        'real proof body); '
        '<span class="badge open">Pending</span> have a typed statement '
        'but no proof yet (<code>[skeleton]/[deferred-heavy]/[GAP]</code>); '
        '<span class="badge muted">Out of scope</span> are claims from '
        'the source paper that the Moore57 closures don’t need '
        '(<code>[out-of-scope]</code>).</p>\n'
        f'<h2>Across all papers</h2>\n'
        f'{progress_bar(overall)}\n'
        f'<p>{progress_caption(overall)}</p>\n'
        '</section>\n'
    )

    for paper in PAPERS:
        key = paper["key"]
        files = per_paper.get(key, [])
        counts = aggregate(files)
        body_parts.append(
            f'<section>\n'
            f'<h2><a href="{key.lower()}.html">{escape(paper["short"])}</a></h2>\n'
            f'<p class="muted" style="margin-bottom:0.4rem">'
            f'<em>{escape(paper["title"])}.</em> {escape(paper["venue"])}. '
            f'DOI: <a href="https://doi.org/{paper["doi"]}">{paper["doi"]}</a>.'
            f'</p>\n'
            f'{progress_bar(counts)}\n'
            f'<p>{progress_caption(counts)} · '
            f'<a href="{key.lower()}.html">section-by-section detail →</a></p>\n'
            f'</section>\n'
        )

    body_parts.append(SITE_FOOT)
    return "".join(body_parts)


def render_status_badge(s: Statement) -> str:
    badge_cls, badge_text = STATUS_BADGE[s.status]
    sub = SUBTAG_LABEL.get(s.subtag, s.subtag)
    return (
        f'<span class="badge {badge_cls}">{badge_text}</span>'
        f' <span class="subtag muted">{escape(sub)}</span>'
    )


def render_paper_page(paper_meta: dict, files: list[FileInfo]) -> str:
    counts = aggregate(files)
    head = site_head(
        title=f'{paper_meta["short"]} — formalization status',
        description=(
            f'Lean formalization status for {paper_meta["short"]} '
            f'({paper_meta["venue"]}).'
        ),
        h1=paper_meta["short"],
        sub=escape(paper_meta["title"]),
        level=1,
    )
    out = [GEN_NOTICE, head]
    out.append(
        '<section>\n'
        f'<p class="muted">{escape(paper_meta["venue"])}. '
        f'DOI: <a href="https://doi.org/{paper_meta["doi"]}">'
        f'{paper_meta["doi"]}</a>.</p>\n'
        f'{progress_bar(counts)}\n'
        f'<p>{progress_caption(counts)} · '
        f'<a href="index.html">all papers</a> · '
        f'<a href="{GITHUB_BLOB}/Moore57/Papers/{paper_meta["key"]}/">browse '
        f'source on GitHub</a></p>\n'
        '</section>\n'
    )

    # Group files by section_key (preserving FileInfo order, which is already
    # in declared section_order from collect()).
    grouped: dict[str, list[FileInfo]] = defaultdict(list)
    for f in files:
        grouped[f.section_key].append(f)
    for section_key, _label in paper_meta["section_order"]:
        section_files = grouped.get(section_key, [])
        if not section_files:
            continue
        sec_counts = {"formalized": 0, "pending": 0, "out_of_scope": 0, "total": 0}
        for f in section_files:
            c = aggregate([f])
            for k in sec_counts:
                sec_counts[k] += c[k]
        if sec_counts["total"] == 0:
            # Section exists only as scaffolding (e.g. Citation.lean with no
            # paper-tied statements). Don't clutter the page.
            continue
        label = section_files[0].section_label
        out.append(f'<section>\n<h2 class="paper-section">{escape(label)}</h2>\n')
        out.append(
            f'<div class="paper-section-bar">'
            f'{progress_bar(sec_counts)}'
            f'<p>{progress_caption(sec_counts)}</p>'
            f'</div>\n'
        )
        for f in section_files:
            github = f"{GITHUB_BLOB}/{f.rel_path.as_posix()}"
            title = f.file_title or f.rel_path.name
            if not f.statements:
                out.append(
                    f'<details class="paper-file empty">\n'
                    f'<summary><strong>{escape(title)}</strong> '
                    f'<span class="muted">— no paper-tied statements</span> '
                    f'<a class="src" href="{github}">.lean</a></summary>\n'
                    f'</details>\n'
                )
                continue
            f_counts = aggregate([f])
            out.append(
                f'<details class="paper-file" open>\n'
                f'<summary><strong>{escape(title)}</strong> '
                f'<span class="muted">— '
                f'{f_counts["formalized"]}/{f_counts["total"]} formalized'
                + (f', {f_counts["pending"]} pending'
                   if f_counts["pending"] else '')
                + (f', {f_counts["out_of_scope"]} out of scope'
                   if f_counts["out_of_scope"] else '')
                + f'</span> '
                f'<a class="src" href="{github}">.lean</a></summary>\n'
                f'<ul class="paper-statements">\n'
            )
            for s in f.statements:
                src_link = f"{github}#L{s.line}"
                summary_html = f' <span class="muted">— {escape(s.summary)}</span>' if s.summary else ''
                out.append(
                    f'<li><span class="stmt-title">{escape(s.title)}</span>'
                    f'{summary_html} {render_status_badge(s)} '
                    f'<a class="src" href="{src_link}">L{s.line}</a></li>\n'
                )
            out.append('</ul>\n</details>\n')
        out.append('</section>\n')

    out.append(SITE_FOOT)
    return "".join(out)


# ---------------------------------------------------------------------------
# index.html summary fragment
# ---------------------------------------------------------------------------


INDEX_START_MARK = "<!-- gen:papers-summary:start -->"
INDEX_END_MARK = "<!-- gen:papers-summary:end -->"


def render_index_fragment(per_paper: dict[str, list[FileInfo]]) -> str:
    overall = {"formalized": 0, "pending": 0, "out_of_scope": 0, "total": 0}
    for files in per_paper.values():
        c = aggregate(files)
        for k in overall:
            overall[k] += c[k]
    rows = []
    for paper in PAPERS:
        files = per_paper.get(paper["key"], [])
        c = aggregate(files)
        rows.append(
            f'    <tr>'
            f'<td><a href="papers/{paper["key"].lower()}.html">'
            f'{escape(paper["short"])}</a></td>'
            f'<td>{c["formalized"]}</td>'
            f'<td>{c["pending"]}</td>'
            f'<td>{c["out_of_scope"]}</td>'
            f'<td>{c["total"]}</td>'
            f'<td style="width:32%">{progress_bar(c)}</td>'
            f'</tr>'
        )
    rows_html = "\n".join(rows)
    return (
        f'{INDEX_START_MARK}\n'
        f'<section>\n'
        f'  <h2>Paper formalization status</h2>\n'
        f'  <p>\n'
        f'    Beyond the group-order tracker above, each of the 5 reference\n'
        f'    papers has its own Lean-mirroring directory under\n'
        f'    <code>Moore57/Papers/&lt;paper&gt;/</code>. Below is the rolled-up\n'
        f'    statement-level status; see\n'
        f'    <a href="papers/index.html">Papers</a> for the §-level drill-down.\n'
        f'  </p>\n'
        f'  <figure>\n'
        f'  <table>\n'
        f'    <thead>\n'
        f'      <tr><th>Paper</th>'
        f'<th>Formalized</th>'
        f'<th>Pending</th>'
        f'<th>Out of scope</th>'
        f'<th>Total</th>'
        f'<th>Progress</th></tr>\n'
        f'    </thead>\n'
        f'    <tbody>\n'
        f'{rows_html}\n'
        f'    </tbody>\n'
        f'    <tfoot>\n'
        f'      <tr><th>All papers</th>'
        f'<th>{overall["formalized"]}</th>'
        f'<th>{overall["pending"]}</th>'
        f'<th>{overall["out_of_scope"]}</th>'
        f'<th>{overall["total"]}</th>'
        f'<th>{progress_bar(overall)}</th></tr>\n'
        f'    </tfoot>\n'
        f'  </table>\n'
        f'  </figure>\n'
        f'</section>\n'
        f'{INDEX_END_MARK}\n'
    )


def patch_index_html(text: str, fragment: str) -> str:
    start = text.find(INDEX_START_MARK)
    end_marker_pos = text.find(INDEX_END_MARK)
    if start != -1 and end_marker_pos != -1 and end_marker_pos > start:
        end = end_marker_pos + len(INDEX_END_MARK)
        # Preserve trailing newline placement: replace exclusive of newline
        # following INDEX_END_MARK so blank-line policy is unchanged.
        return text[:start] + fragment.rstrip("\n") + text[end:]
    # No sentinels yet: inject right before the "Reference" section, or
    # before the closing </main> if the section isn't found.
    anchor = text.find('<section>\n  <h2>Reference</h2>')
    if anchor != -1:
        return text[:anchor] + fragment + text[anchor:]
    anchor = text.find('<footer class="site">')
    if anchor != -1:
        return text[:anchor] + fragment + text[anchor:]
    return text + fragment


# ---------------------------------------------------------------------------
# Nav patch: add "Papers" between "Top" and "About" in existing pages
# ---------------------------------------------------------------------------

NAV_BLOCK_RE = re.compile(
    r'(<header class="site">.*?</header>)', re.DOTALL
)
NAV_INSERT_RE = re.compile(
    r'(<li><a href="index\.html">[^<]*Top</a></li>\n)(\s*)<li><a href="about\.html">About</a></li>'
)
NAV_PAPERS_LINE = '<li><a href="papers/index.html">Papers</a></li>\n'


def ensure_papers_in_nav(text: str) -> str:
    """Insert the Papers link inside the site header nav only. We can't
    use a global 'is link present' check because the body of index.html
    legitimately links to papers/index.html in its summary table."""
    m = NAV_BLOCK_RE.search(text)
    if not m:
        return text
    header = m.group(1)
    if 'href="papers/index.html"' in header:
        return text
    new_header = NAV_INSERT_RE.sub(
        lambda mm: mm.group(1) + mm.group(2) + NAV_PAPERS_LINE + mm.group(2)
                   + '<li><a href="about.html">About</a></li>',
        header,
    )
    if new_header == header:  # nav didn't match (unexpected layout)
        return text
    return text[:m.start()] + new_header + text[m.end():]


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def write_or_check(path: Path, content: str, *, check: bool) -> bool:
    """Return True if the path differs (or, in check mode, would differ)."""
    if path.exists():
        existing = path.read_text(encoding="utf-8")
    else:
        existing = None
    if existing == content:
        return False
    if check:
        if existing is None:
            print(f"[check] would create {path.relative_to(ROOT)}")
        else:
            print(f"[check] would update {path.relative_to(ROOT)}")
            diff = difflib.unified_diff(
                existing.splitlines(keepends=True),
                content.splitlines(keepends=True),
                fromfile=str(path), tofile=str(path) + " (new)",
                n=2,
            )
            sys.stdout.writelines(list(diff)[:80])
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    return True


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if any generated file would change")
    args = ap.parse_args()

    per_paper = collect()

    drift = False

    # docs/papers/index.html
    content = render_papers_index(per_paper)
    if write_or_check(PAPERS_OUT / "index.html", content, check=args.check):
        drift = True

    # docs/papers/<paper>.html
    for paper in PAPERS:
        files = per_paper.get(paper["key"], [])
        content = render_paper_page(paper, files)
        target = PAPERS_OUT / f'{paper["key"].lower()}.html'
        if write_or_check(target, content, check=args.check):
            drift = True

    # Patch docs/index.html, docs/about.html, docs/contribute.html
    fragment = render_index_fragment(per_paper)
    index_text = INDEX_PATH.read_text(encoding="utf-8")
    new_text = patch_index_html(index_text, fragment)
    new_text = ensure_papers_in_nav(new_text)
    if write_or_check(INDEX_PATH, new_text, check=args.check):
        drift = True

    for nav_target in ("about.html", "contribute.html"):
        p = DOCS_DIR / nav_target
        if not p.exists():
            continue
        txt = p.read_text(encoding="utf-8")
        new = ensure_papers_in_nav(txt)
        if write_or_check(p, new, check=args.check):
            drift = True

    if args.check and drift:
        print(
            "\n[check] docs/papers/* is stale. Run "
            "`python3 bin/gen_papers_status.py` and commit.",
            file=sys.stderr,
        )
        return 1
    if not args.check and drift:
        # Print a short tally so it's obvious what changed.
        overall = {"formalized": 0, "pending": 0, "out_of_scope": 0, "total": 0}
        for files in per_paper.values():
            c = aggregate(files)
            for k in overall:
                overall[k] += c[k]
        print(
            f"papers status: {overall['formalized']} formalized · "
            f"{overall['pending']} pending · "
            f"{overall['out_of_scope']} out of scope · "
            f"{overall['total']} total"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
