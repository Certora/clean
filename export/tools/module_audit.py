#!/usr/bin/env python3
"""Module audit of the Lean port (`export/CCLib`).

Classifies every `CCLib.*` module -- those whose `.lean` file exists and those
that are imported somewhere but missing -- against the original Rocq/OCaml
sources of the repository, and prints a JSON summary used to write
`MODULE_AUDIT.md`.

Usage (from the repository root):  python3 export/tools/module_audit.py [--json]
"""
import glob, json, os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
os.chdir(ROOT)

TARGETS = ['aarch64', 'arm', 'powerpc', 'riscV', 'x86']
SRC_EXT = ('.v', '.vp', '.vy', '.ml', '.mli', '.mll', '.mly')

def rocq_files(d):
    if not os.path.isdir(d):
        return set()
    return {os.path.splitext(f)[0] for f in os.listdir(d) if f.endswith(SRC_EXT)}

ROCQ = {}
for d in ['lib', 'common', 'cfrontend', 'backend', 'driver', 'cparser', 'debug',
          'extraction', 'MenhirLib', 'x86_32', 'x86_64'] + TARGETS:
    ROCQ[d] = rocq_files(d)
for d in glob.glob('flocq/*'):
    if os.path.isdir(d):
        ROCQ[d] = rocq_files(d)
ROCQ['flocq'] = rocq_files('flocq')

# ---------------------------------------------------------------- import graph
lean_files = [f for f in glob.glob('export/**/*.lean', recursive=True)] + \
             glob.glob('test/**/*.lean', recursive=True) + ['main.lean']

def modname(path):
    p = path
    for pre in ('export/examples/', 'export/', 'test/', ''):
        if p.startswith(pre):
            return p[len(pre):-5].replace('/', '.')
    return None

present = {}
for f in glob.glob('export/CCLib/**/*.lean', recursive=True):
    present[modname(f)] = f

IMPORT_RE = re.compile(r'^(--\s*(?:unavailable:|missing \(to port\):|blocked:)\s*)?import\s+([\w.]+)', re.M)
imports = {}      # module file -> list of (module, commented?)
for f in lean_files:
    try:
        txt = open(f, encoding='utf-8').read()
    except FileNotFoundError:
        continue
    imports[f] = [(m.group(2), bool(m.group(1))) for m in IMPORT_RE.finditer(txt)]

importers = {}
for f, lst in imports.items():
    for m, _ in lst:
        importers.setdefault(m, set()).add(f)

# Modules listed as missing when the checkout was first analysed (the first
# `MISSING_MODULES.md`); kept so that modules removed from the import lists
# because they should not exist are still reported.
BASELINE = [l.strip() for l in open('export/tools/missing_modules_baseline.txt') if l.strip()]
missing = sorted(set(m for m in importers if m.startswith('CCLib.') and m not in present) |
                 set(m for m in BASELINE if m.startswith('CCLib.') and m not in present))

# -------------------------------------------------------------- classification
FLOCQ_REPLACED = re.compile(r'^(IEEE754_extra|FloatsParsed|FloatsReal)')
CORE_DUP = {
    'Axioms': 'Lean core has `funext`, `propext`, `Classical.choice` and proof irrelevance built in',
    'Zbits': '`CCLib.lib.Integers*` is built on core `BitVec`/`Int` bit operations (`Int.testBit`, `<<<`, `Int.land` ...); see MATHLIB_DUPLICATION.md',
    'Intv': '`Intv.In` is `Set.Ico` (Mathlib) / `List.range\'` (core)',
    'Coqlib': 'mostly core/Batteries/Mathlib list and arithmetic lemmas (`List.Forall₂`, `Option.Rel`, `Int.fdiv`, `List.Nodup` ...); see MATHLIB_DUPLICATION.md',
    'CoqlibMore': 'same as `Coqlib` (`List.Disjoint`, `List.IsSuffix`, `Prod.Lex`, `List.foldl` ...)',
    'Wfsimpl': 'is `WellFounded.fix` / `WellFounded.fix_eq` (core)',
    'BoolEqual': 'is `deriving DecidableEq` (core)',
    'Decidableplus': 'is `Decidable` + `decide` (core)',
}

def base_dir(mod):
    parts = mod.split('.')
    if parts[1] == 'flocq':
        return 'flocq/' + parts[2] if len(parts) > 3 else 'flocq', parts[-1]
    return parts[1], parts[-1]

def prefix_match(name, names):
    best = None
    for n in names:
        if name.startswith(n) and name != n and (best is None or len(n) > len(best)):
            best = n
    return best

# Manual verdicts, where the file-name heuristic below is wrong.
OVERRIDES = {
    'CCLib.common.Simulation': ('chunk', 'split chunk of `common/Smallstep` (forward simulations) and `common/Behaviors`'),
    'CCLib.common.BackwardSimulation': ('chunk', 'split chunk of `common/Smallstep` (backward simulations) and `common/Behaviors`'),
    'CCLib.common.ForwardToBackward': ('chunk', 'split chunk of `common/Smallstep` (section `FORWARD_TO_BACKWARD`)'),
    'CCLib.common.SimulationEventually': ('chunk', 'split chunk of `common/Smallstep` (`eventually` diagrams)'),
    'CCLib.common.SimulationDeterm': ('chunk', 'split chunk of `common/Smallstep` (simulations of determinate semantics)'),
    'CCLib.common.Bigstep': ('chunk', 'split chunk of `common/Smallstep` / `common/Behaviors` (big-step semantics, `forever`)'),
    'CCLib.common.DetermTac': ('keep', 'proof-automation helper (Lean counterpart of the `Determ` Ltac of the Rocq files)'),
    'CCLib.common.Worlds': ('chunk', 'split chunk of `common/Determinism` (deterministic worlds)'),
    'CCLib.driver.BackendCorrect': ('chunk', 'split chunk of `driver/Compiler` (back-end correctness)'),
    'CCLib.lib.Positive': ('keep', "Rocq standard library `positive` (needed: every `ident`/`block`/`PTree` key); equivalent to Mathlib `PosNum`"),
    'CCLib.lib.FSetAVLTree': ('chunk', 'split chunk of `CCLib.lib.FSetAVL` (Rocq standard library `MSetAVL`)'),
    'CCLib.lib.FSetAVL': ('keep', 'Rocq standard library `MSetAVL`, included by `lib/FSetAVLplus.v`; could later be replaced by core `Std.TreeSet`'),
    'CCLib.lib.FloatModel': ('replace-by-core-later', 'backport of core `Float.Model` (Lean ≥ v4.33); delete once the toolchain is upgraded'),
    'CCLib.lib.FloatModelLemmas': ('replace-by-core-later', 'pack/unpack lemmas of the `Float.Model` backport; delete or shrink once the toolchain is upgraded'),
    'CCLib.lib.IEEE754_extra': ('keep', '`lib/IEEE754_extra` (integer part), restated on `FloatModel` instead of Flocq'),
    'CCLib.lib.FloatsParsed': ('chunk', 'split chunk of `lib/Floats` (`from_parsed`, float literals); port on `FloatModel`'),
    'CCLib.lib.Format': ('keep', 'model of the OCaml standard library `Format` used by the printers (`Print*.ml`)'),
    'CCLib.lib.OCamlHashtbl': ('keep', 'model of the OCaml standard library `Hashtbl` (iteration order needed by `debug/`)'),
    'CCLib.lib.MathlibEquiv': ('keep', 'bridge theorems port ↔ Mathlib (root of `CCLibMathlib`)'),
    'CCLib.common.Errors': ('keep', '`common/Errors`; `Res` is core `Except String` up to names'),
    'CCLib.backend.Registers': ('merged', '`backend/Registers` is merged into `backend/RTL.lean` (`Reg`, `Regmap`)'),
    'CCLib.arm.Archi': ('merged', 'merged into `CCLib.targets.Archi` (`ArchiConfig` of every target)'),
    'CCLib.powerpc.Archi': ('merged', 'merged into `CCLib.targets.Archi`'),
    'CCLib.riscV.Archi': ('merged', 'merged into `CCLib.targets.Archi`'),
    'CCLib.x86_32.Archi': ('merged', 'merged into `CCLib.targets.Archi`'),
    'CCLib.x86_64.Archi': ('merged', 'merged into `CCLib.targets.Archi`'),
    'CCLib.riscV.Conventions1': ('merged', 'merged into `CCLib.riscV.Conventions` (port of `riscV/Conventions1.v`)'),
    'CCLib.x86.Conventions1': ('merged', 'merged into `CCLib.x86.Conventions` (port of `x86/Conventions1.v`)'),
    'CCLib.riscV.Conventions': ('keep', 'port of `riscV/Conventions1.v`, merged with the RISC-V instance of `backend/Conventions.v`'),
    'CCLib.x86.Conventions': ('keep', 'port of `x86/Conventions1.v`, merged with the x86 instance of `backend/Conventions.v`'),
    'CCLib.common.BehaviorsInfSeq': ('merged', 'merged into `CCLib.common.Bigstep` (`foreverReactive_coind`, `forever_silent_or_reactive`, proved directly without the `tstate` device of section `INF_SEQ_DECOMP`)'),
    'CCLib.common.Builtins0': ('merged', 'merged into `CCLib.common.Builtins` (port of `common/Builtins0.v` and the target `Builtins1.v`)'),
    'CCLib.aarch64.Builtins1': ('merged', 'merged into `CCLib.common.Builtins` (`PlatformBuiltin`: aarch64 has no platform built-ins)'),
    'CCLib.riscV.Builtins1': ('merged', 'identical to `aarch64/Builtins1.v` (no platform built-ins): `PlatformBuiltin` of `CCLib.common.Builtins`'),
    'CCLib.arm.Builtins1': ('merged', 'identical to `aarch64/Builtins1.v` (no platform built-ins): `PlatformBuiltin` of `CCLib.common.Builtins`'),
    'CCLib.x86.Builtins1': ('merged', 'merged into `CCLib.x86.SelectOp` (`__builtin_fmax`/`__builtin_fmin`)'),
    'CCLib.cparser.pre_parser': ('merged', 'merged into `CCLib.cparser.PreParser` (recursive-descent port of `cparser/pre_parser.mly`)'),
    'CCLib.cparser.pre_parser_aux': ('merged', 'merged into `CCLib.cparser.PreParser` (`identifier_type`, typedef context)'),
    'CCLib.cparser.ErrorReports': ('merged', 'merged into `CCLib.cparser.PreParser` (`syntaxError`, without the message database)'),
    'CCLib.cparser.PreParser': ('keep', 'port of `cparser/pre_parser.mly`, `cparser/pre_parser_aux.ml`, `cparser/ErrorReports.ml` and `tokens_stream` of `cparser/Lexer.mll`'),
    'CCLib.riscV.BackendCorrect': ('drop-target-copy', 'per-target copy of `driver/BackendCorrect` + `driver/FrontendCorrect`'),
    'CCLib.x86.BackendCorrect': ('drop-target-copy', 'per-target copy of `driver/BackendCorrect` + `driver/FrontendCorrect`'),
}
for _t in ('riscV', 'x86', 'aarch64'):
    for _n in ('Inliningaux', 'RTLgenaux', 'Selectionaux'):
        OVERRIDES[f'CCLib.{_t}.{_n}'] = ('drop-target-copy', f'per-target copy of `backend/{_n}.ml`')
for _n in ('Alg', 'BofZ', 'Bparse', 'Conv', 'RoundOdd', 'ZofB'):
    OVERRIDES[f'CCLib.lib.IEEE754_extra{_n}'] = ('drop-flocq', 'Flocq-based chunk of `lib/IEEE754_extra`; the results `Floats.v` needs go into `IEEE754_extra.lean`, stated on `FloatModel`')

def classify(mod):
    if mod in OVERRIDES:
        return OVERRIDES[mod]
    return classify0(mod)

def classify0(mod):
    """Return (verdict, reason).  verdict in
    keep | chunk | drop-flocq | drop-extraction | drop-core | drop-target-copy |
    drop-not-rocq | not-a-module"""
    d, name = base_dir(mod)
    if d == 'flocq' or d.startswith('flocq/'):
        return 'drop-flocq', 'Flocq is replaced by the exact IEEE-754 model (`CCLib.lib.FloatModel`, backport of core `Float.Model`)'
    if d == 'lib' and FLOCQ_REPLACED.match(name):
        return 'drop-flocq', 'Flocq-level float theory; `CCLib.lib.Floats*` compute on bit patterns through `FloatModel`'
    if d == 'extraction' or name == 'extractionMachdep':
        return 'drop-extraction', 'Rocq→OCaml extraction directives; a Lean port is executable as is'
    if d == 'lib' and name in CORE_DUP:
        return 'drop-core', CORE_DUP[name]
    if d in TARGETS:
        tf = ROCQ[d]
        if name in tf:
            return 'keep', f'`{d}/{name}` exists in Rocq'
        pm = prefix_match(name, tf)
        if pm:
            return 'chunk', f'split chunk of `{d}/{pm}`'
        if name in ROCQ['backend']:
            return 'drop-target-copy', f'per-target copy of target-independent `backend/{name}`'
        pm = prefix_match(name, ROCQ['backend'])
        if pm:
            return 'drop-target-copy', f'per-target copy of a chunk of `backend/{pm}`'
        if name in ROCQ['driver'] or prefix_match(name, ROCQ['driver']):
            return 'drop-target-copy', f'per-target copy of `driver/{prefix_match(name, ROCQ["driver"]) or name}`'
        return 'drop-not-rocq', f'no counterpart in Rocq `{d}/` or `backend/`'
    if d in ('targets', 'logic'):
        return 'keep', 'not a CompCert file (port infrastructure / VST-style program logic)'
    tf = ROCQ.get(d, set())
    if name in tf:
        return 'keep', f'`{d}/{name}` exists in Rocq'
    pm = prefix_match(name, tf)
    if pm:
        return 'chunk', f'split chunk of `{d}/{pm}`'
    return 'drop-not-rocq', f'no counterpart in Rocq `{d}/`'

def lines(f):
    with open(f, encoding='utf-8') as h:
        return sum(1 for _ in h)

def real_importers(m):
    return sorted(f for f in importers.get(m, ()) if f not in ('export/CCLib.lean', 'export/CCLibReal.lean'))

res = {'missing': [], 'present': []}
for m in missing:
    v, r = classify(m)
    res['missing'].append(dict(module=m, verdict=v, reason=r, importers=real_importers(m)))
for m, f in sorted(present.items()):
    v, r = classify(m)
    res['present'].append(dict(module=m, verdict=v, reason=r, file=f, lines=lines(f),
                               importers=real_importers(m)))

if '--json' in sys.argv:
    json.dump(res, sys.stdout, indent=1)
else:
    from collections import Counter
    for k in ('missing', 'present'):
        c = Counter(x['verdict'] for x in res[k])
        print(k, len(res[k]), dict(c))


# ------------------------------------------------------------ MISSING_MODULES.md
def rocq_source(mod):
    d, name = base_dir(mod)
    tf = ROCQ.get(d, set())
    def ext(n):
        for e in SRC_EXT:
            if os.path.exists(f'{d}/{n}{e}'):
                return f'{d}/{n}{e}'
        return f'{d}/{n}'
    if name in tf:
        return ext(name)
    pm = prefix_match(name, tf)
    if pm:
        return ext(pm)
    return ''

def missing_md():
    from collections import defaultdict
    out = []
    w = out.append
    miss = res['missing']
    keep = [x for x in miss if x['verdict'] in ('keep', 'chunk')]
    drop = [x for x in miss if x['verdict'] not in ('keep', 'chunk')]
    w('# Modules imported by the port but missing from this checkout\n')
    w('Generated by `python3 export/tools/module_audit.py --missing-md` (repository root), which')
    w('scans every `import` line of `export/`, `test/` and `main.lean` and classifies each')
    w('`CCLib.*` module that has no source file against the Rocq/OCaml sources of the')
    w('repository.  The analysis behind the verdicts, and the same analysis for the modules')
    w('that exist, is in `MODULE_AUDIT.md`.\n')
    w(f'Missing modules: **{len(miss)}**, of which **{len(keep)} should be ported** and')
    w(f'**{len(drop)} should not exist** in the Lean port.  `export/CCLib.lean` lists the')
    w('first group as `-- missing (to port): import …`; the second group has been removed')
    w('from it (their remaining importers, if any, are listed below and must be refactored).\n')
    w('## 1. Modules to port\n')
    w('Priority **P1**: a present module imports it (porting it unblocks that module);')
    w('**P2**: a Rocq top-level file (`*proof.v` etc.) that is only an umbrella over chunks')
    w('that already exist, or a remaining chunk of a ported file; **P3**: the ARM / PowerPC')
    w('target-specific files (these need the target-generic back end first, see')
    w('`MODULE_AUDIT.md` §4).\n')
    groups = defaultdict(list)
    for x in keep:
        groups[x['module'].split('.')[1]].append(x)
    for g in sorted(groups):
        w(f'### `{g}`\n')
        w('| module | Rocq/OCaml source | kind | priority | present importers |')
        w('|---|---|---|---|---|')
        for x in groups[g]:
            imp = x['importers']
            pr = 'P1' if imp else ('P3' if g in ('arm', 'powerpc') else 'P2')
            kind = 'whole file' if x['verdict'] == 'keep' else 'chunk'
            imps = ', '.join(f'`{i}`' for i in imp) if imp else ''
            w(f"| `{x['module']}` | `{rocq_source(x['module'])}` | {kind} | {pr} | {imps} |")
        w('')
    w('## 2. Modules that should not exist\n')
    titles = {
        'drop-target-copy': 'Per-target copies of target-independent back-end / driver files (Rocq compiles `backend/*.v` once against the configured target; the port must make `backend/` generic in the target instead)',
        'drop-flocq': 'Flocq and Flocq-based float theory (replaced by the exact IEEE-754 model `CCLib.lib.FloatModel`, a backport of core `Float.Model`)',
        'drop-extraction': 'Rocq → OCaml extraction (Lean code is executable as it stands)',
        'drop-core': 'Duplicates of Lean core / Batteries / Mathlib',
        'merged': 'Already merged into another module of the port',
        'drop-not-rocq': 'No Rocq / OCaml counterpart',
    }
    by = defaultdict(list)
    for x in drop:
        by[x['verdict']].append(x)
    for v in ['drop-flocq', 'drop-extraction', 'drop-core', 'merged', 'drop-not-rocq', 'drop-target-copy']:
        if not by[v]:
            continue
        w(f'### {titles[v]} — {len(by[v])} modules\n')
        if v == 'drop-target-copy':
            per = defaultdict(list)
            for x in by[v]:
                per[x['module'].split('.')[1]].append(x['module'].split('.')[-1])
            for t in sorted(per):
                w(f'* `CCLib.{t}.*` ({len(per[t])}): ' + ', '.join(f'`{n}`' for n in per[t]))
            imp = [x for x in by[v] if x['importers']]
            if imp:
                w('\nPresent importers that must be refactored: ' + '; '.join(
                    f"`{x['module']}` ← " + ', '.join(f'`{i}`' for i in x['importers']) for x in imp))
            w('')
            continue
        w('| module | reason | present importers (to refactor) |')
        w('|---|---|---|')
        for x in by[v]:
            imps = ', '.join(f'`{i}`' for i in x['importers'])
            w(f"| `{x['module']}` | {x['reason']} | {imps} |")
        w('')
    w('## 3. Present modules that do not build because they import a missing module\n')
    w('| module | missing modules it (transitively) needs |')
    w('|---|---|')
    pres = {x['module'] for x in res['present']}
    R = re.compile(r'^import\s+([\w.]+)', re.M)
    dep = {x['module']: [m for m in R.findall(open(x['file'], encoding='utf-8').read()) if m.startswith('CCLib.')]
           for x in res['present']}
    memo = {}
    def need(m):
        if m in memo:
            return memo[m]
        memo[m] = set()
        if m not in pres:
            memo[m] = {m}
            return memo[m]
        s = set()
        for d in dep[m]:
            s |= need(d)
        memo[m] = s
        return s
    for m in sorted(pres):
        s = need(m)
        if s:
            w(f"| `{m}` | " + ', '.join(f'`{x}`' for x in sorted(s)) + ' |')
    w('')
    return '\n'.join(out)

if '--missing-md' in sys.argv:
    open('MISSING_MODULES.md', 'w', encoding='utf-8').write(missing_md())
    print('wrote MISSING_MODULES.md')
