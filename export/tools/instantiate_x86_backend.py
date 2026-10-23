import re, os, sys, glob
# usage (from anywhere): python3 instantiate_x86_backend.py Mod1 Mod2 ...
# Copies CCLib/backend/ModX.lean to CCLib/x86/ModX.lean, re-targeting it to the
# x86-64 back end (namespace `CC.X86`).
#
# The aarch64 back end threads the ABI flag `abi : AbiKind` through every
# definition that depends on `loc_arguments`.  On x86-64 the corresponding
# Rocq `Parameter` is `Archi.win64`, which in addition changes the callee-save
# registers (`is_callee_save`, `destroyed_at_call`, the allocatable registers)
# and the stack layout (`fe_ofs_arg`).  Two treatments are therefore used:
#   * files whose `abi` only reaches the value analysis (where it decides
#     `parameter_needs_normalization`, always `false` on x86-64) drop it, as
#     the RISC-V instance does, and use the aarch64 `.Apple` ABI, which needs
#     no parameter normalization;
#   * every other file renames `abi : AbiKind` to `win64 : Bool`, and the
#     uses of the win64-dependent x86 functions get the extra `win64`
#     argument.
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
TARGET = 'x86'
NS = 'X86'
NAME = 'x86-64'
mods = sys.argv[1:]
tdir = f'CCLib/{TARGET}'
existing = set(os.path.basename(f)[:-5] for f in glob.glob(f'{tdir}/*.lean'))
A64MAP = {'OpLessdef': 'OpInject', 'ValueAOpproof': 'ValueAOp', 'NeedOpProof': 'NeedOp',
          'Conventions1': 'Conventions'}
STRIP = re.compile(r'^(ValueAnalysis|CSE|Constprop|Deadcode)')
# x86 functions taking `win64` whose aarch64 versions take no ABI argument
W64FUNS = ['isCalleeSave', 'intCallerSaveRegs', 'floatCallerSaveRegs', 'intCalleeSaveRegs',
           'floatCalleeSaveRegs', 'destroyedAtCall', 'allocatableRegisters', 'LocArgumentAcceptable',
           'CalleeSaveLoc', 'AgreeCalleeSave', 'feOfsArg', 'undefCallerSaveRegs',
           'locmap_get_set_loc_result', 'locmap_get_set_loc_result_callee_save',
           'locResult_callerSave', 'returnRegs', 'noCallerSaves', 'rosCompatibleTailcall',
           'offsetArg', 'NoCalleeSaves', 'ExtcallArg', 'ExtcallArgPair']


KW = {'exact', 'apply', 'refine', 'rw', 'simp', 'have', 'obtain', 'calc', 'show', 'from', 'then',
      'else', 'at', 'using', 'with', 'intro', 'return', 'if', 'in', 'by', 'match', 'fun', 'let',
      'suffices', 'unfold', 'generalize', 'rcases', 'cases', 'induction', 'specialize', 'use',
      'exists', 'constructor', 'def', 'theorem', 'lemma', 'abbrev', 'inductive', 'structure',
      'instance', 'where', 'do', 'only', 'not', 'and', 'or'}


def strip_abi(s, m):
    s = s.replace('einitRegs abi', 'einitRegs .Apple')
    s = s.replace('have EM := ematch_init (bc := bc) abi f.fn_params vl f.fn_sig.sig_args ht hv',
                  'have EM : Ematch bc (initRegs vl f.fn_params)\n      (einitRegs .Apple f.fn_params f.fn_sig.sig_args) := by\n    rw [initRegs_eq_shared]; exact ematch_init (bc := bc) .Apple f.fn_params vl f.fn_sig.sig_args ht hv')
    if m == 'ValueAnalysisSoundBasic':
        s = s.replace('/-! ## Properties of the dataflow solution -/', '''omit o in
/-- The {NAME} `RTL.init_regs` is the same function as the shared one used by
    `ValueDomain.ematch_init`. -/
theorem initRegs_eq_shared : ∀ (vl : List Val) (rl : List Reg),
    RTL.initRegs vl rl = CC.RTL.initRegs vl rl
  | _ :: vs, _ :: rs => by simp only [RTL.initRegs, CC.RTL.initRegs, initRegs_eq_shared vs rs]
  | [], _ => rfl
  | _ :: _, [] => rfl

/-! ## Properties of the dataflow solution -/'''.replace('{NAME}', NAME))
    s = re.sub(r'[ \t]*[\(\{]abi\s*:\s*[\w.]*AbiKind[\)\}]', '', s)
    s = re.sub(r'\(abi\s*:=\s*abi\)', '', s)
    s = re.sub(r'^\s*omit abi in\n', '', s, flags=re.M)
    s = re.sub(r'^\s*include abi\n', '', s, flags=re.M)
    s = re.sub(r'(?<=[ \t(])abi(?=[\s)\],])', '', s)
    s = re.sub(r'^[ \t]*variable[ \t]*\n', '', s, flags=re.M)
    return s


def rename_abi(s):
    s = re.sub(r'([\(\{])abi\s*:\s*[\w.]*AbiKind([\)\}])', r'\1win64 : Bool\2', s)
    s = re.sub(r'\(abi\s*:=\s*abi\)', '(win64 := win64)', s)
    s = re.sub(r'(?<![\w.])abi(?![\w])', 'win64', s)
    # extra `win64` argument of the x86 functions that depend on it
    out = []
    for line in s.split('\n'):
        st = line.lstrip()
        if st.startswith(('unfold ', 'delta ', '--', 'open ', 'import ')) or '`' in line:
            out.append(line)
            continue
        for fn in W64FUNS:
            def add(mo):
                pre = line[:mo.start()]
                if re.search(r'(def|theorem|lemma|abbrev|structure|inductive|instance)\s+$', pre):
                    return mo.group(0)
                # inside a simp/rw lemma list: leave the bare name
                post = line[mo.end():].lstrip()
                if pre.count('[') > pre.count(']') and re.search(r'(simp|rw|unfold|simp_all|dsimp|simp only)[^\n]*\[[^\]]*$', pre) \
                        and (post[:1] in (',', ']', '') or re.match(r'at\b', post)):
                    return mo.group(0)
                pw = re.search(r'([\w\')]+)\s+$', pre)
                if pw and pw.group(1) not in KW:
                    return '(' + mo.group(0) + ' win64)'
                return mo.group(0) + ' win64'
            line = re.sub(r'(?<![\w.])((?:[A-Z]\w*\.)*' + fn + r')(?![\w.\'])(?!\s+win64)(?=[\s)\],]|$)', add, line)
        for fn in W64FUNS:
            line = re.sub(r'(?<![\w.])((?:Conventions1?\.)?' + fn + r')\.(?=[a-z])', r'(\1 win64).', line)
        out.append(line)
    s = '\n'.join(out)
    # the x86 `Bounds` record is indexed by `win64`
    s = re.sub(r'(?<![\w.])((?:Bounds\.)?Bounds)(?=[\s)\]])(?!\s+win64)', r'\1 win64', s)
    s = s.replace('structure Bounds win64 where', 'structure Bounds where')
    if re.search(r'(?<![\w.])win64(?![\w])', s):
        s = s.replace(f'\nnamespace {NS}\n', f'\nnamespace {NS}\n\n/- `Archi.win64` (a Rocq `Parameter`): whether the Windows x86-64 ABI is used. -/\nvariable (win64 : Bool)\n', 1)
    return s


def fix_refs(s, m):
    s = s.replace(f'import CCLib.{TARGET}.CombineOp\n', f'import CCLib.{TARGET}.CombineOp\nimport CCLib.{TARGET}.CSEdomain\n') if m != 'CSEdomain' else s
    s = re.sub(r'(?<![\w.])evalOperation_preserved', 'Op.evalOperation_preserved', s)
    s = re.sub(r'(?<![\w.])evalAddressing_preserved', 'Op.evalAddressing_preserved', s)
    s = s.replace('CleanupLabelsproof.listNthZ_mem', 'CminorSel.listNthZ_mem')
    s = s.replace('CC.evalOperation_preserved', 'Op.evalOperation_preserved')
    s = s.replace('CC.evalAddressing_preserved', 'Op.evalAddressing_preserved')
    if m == 'Stacking':
        s = s.replace(f'import CCLib.{TARGET}.Stacklayout\n', f'import CCLib.{TARGET}.Stacklayout\nimport CCLib.{TARGET}.Mach\n')
    s = s.replace('by simp [Mreg.type, ATyp.size]', 'by rw [Mreg.type_eq_any64]; decide')
    s = s.replace('''    have AL1 : alignChunk (Chunk.ofTyp (Mreg.type r)) ∣ align pos (Mreg.type r).size :=
      Int.dvd_trans''', '''    have AL1 : alignChunk (Chunk.ofTyp (Mreg.type r)) ∣ align pos (Mreg.type r).size := by
      rw [Mreg.type_eq_any64]; exact Int.dvd_trans''')
    s = s.replace('''    destroyedByStore (simplifyStore chunk) addr = destroyedByStore chunk addr := rfl''',
                  '''    destroyedByStore (simplifyStore chunk) addr = destroyedByStore chunk addr := by
  cases chunk <;> rfl''')
    if m == 'StackingproofStep':
        s = stackingstep_fix(s)
    # `Msetstack` of a `Tany64` register destroys no register on x86-64
    s = s.replace('star_left (Mach.Step.Msetstack _ _ _ _ _ _ _ _ _ _ _ STORE rfl) A rfl',
                  'star_left (Mach.Step.Msetstack _ _ _ _ _ _ _ _ _ _ rs STORE\n        (by rw [Mreg.type_eq_any64]; rfl)) A rfl')
    s = s.replace('''/-- On aarch64 every machine register has type `Tany64`, so any value fits. -/
theorem hasType_mreg (v : Val) (r : Mreg) : Val.HasType v (Mreg.type r) := by
  cases v <;> rfl''', '''/-- On x86-64 every machine register has type `Tany64`, so any value fits. -/
theorem hasType_mreg (v : Val) (r : Mreg) : Val.HasType v (Mreg.type r) := by
  rw [Mreg.type_eq_any64]; cases v <;> rfl''')
    return s


def fix_recursive(s):
    # inside its own (recursive) definition a declaration is not applied to
    # the section variable `win64`
    parts = re.split(DECL, s)
    out = []
    for d in parts:
        mo = re.match(DHEAD, d)
        if mo and mo.group(1) != 'structure' and not re.search(r'[({]win64\s*:', head(d, 'theorem')):
            n = re.escape(mo.group(2).split('.')[-1])
            k = d.find('\n')
            e = len(d)
            if mo.group(1) == 'inductive':
                e = d.find('\n\n')
                e = len(d) if e < 0 else e
            body = re.sub(r'\((' + n + r') win64\)', r'\1', re.sub(r'(?<![\w.])(' + n + r') win64(?![\w])', r'\1', d[k:e]))
            d = d[:k] + body + d[e:]
        out.append(d)
    return '\n'.join(out)


def stackingstep_fix(s):
    # x86 `Lsetstack`/`Msetstack` of a float destroy `FP0`
    # (`destroyed_by_setstack`), and `Mstore` destroys the registers of the
    # simplified chunk
    i = s.index('  | Lsetstack s f sp src sl ofs ty b rs m rs\' e =>')
    j = s.index('  | Lop s f sp op args res b rs m v rs\' hev e =>')
    blk = s[i:j]
    for a, b in [('frame_set_local SEP BOUND', 'frame_set_local (frame_undef_regs (destroyedBySetstack ty) SEP) BOUND'),
                 ('frame_set_outgoing SEP BOUND', 'frame_set_outgoing (frame_undef_regs (destroyedBySetstack ty) SEP) BOUND'),
                 ('(agree_regs_set_slot _ _ _ _ AGREGS)',
                  '(agree_regs_set_slot _ _ _ _ (agree_regs_undef_regs (destroyedBySetstack ty) AGREGS))'),
                 ('(agree_locs_set_slot _ _ _ AGLOCS rfl)',
                  '(agree_locs_set_slot _ _ _ (agree_locs_undef_locs (destroyedBySetstack ty) AGLOCS\n              (destroyed_by_setstack_caller_save win64 ty)) rfl)')]:
        blk = blk.replace(a, b)
    s = s[:i] + blk + s[j:]
    s = s.replace('''          (agree_regs_undef_regs (destroyedByStore chunk addr) AGREGS)''',
                  '''          (by rw [simplify_store_destroyed, transl_destroyed_by_store]
              exact agree_regs_undef_regs (destroyedByStore chunk addr) AGREGS)''')
    return s


def bounds_fix(s):
    s = s.replace('structure Bounds where', 'structure Bounds (win64 : Bool) where')
    s = s.replace('section WITHIN_BOUNDS\nvariable (win64 : Bool) (b : Bounds win64)\n',
                  'section WITHIN_BOUNDS\nvariable {win64 : Bool} (b : Bounds win64)\n')
    s = s.replace("/-- `Bounds.instr_within_bounds` -/\ndef InstrWithinBounds (i : Instruction) : Prop :=",
                  "end WITHIN_BOUNDS\n\n/-- `Bounds.instr_within_bounds` -/\ndef InstrWithinBounds (win64 : Bool) (b : Bounds win64) (i : Instruction) : Prop :=")
    s = s.replace('  | _ => True\n\nend WITHIN_BOUNDS\n', '  | _ => True\n')
    s = s.replace('/-! ## Size of the callee-save area and frame environments -/\n',
                  '/-! ## Size of the callee-save area and frame environments -/\n\nvariable {win64 : Bool}\n')
    s = s.replace('  * `Archi.abi` (used by `size_arguments`) is an explicit argument `win64`.',
                  '  * `Archi.win64` (a Rocq `Parameter`, used by `size_arguments` and\n    `is_callee_save`) is an explicit argument `win64`; the `Bounds` record is\n    indexed by it, since `used_callee_save_prop` refers to `is_callee_save`.')
    return s


def gen(m):
    src = f'CCLib/backend/{m}.lean'
    s = open(src).read()

    def imp(mo):
        full = mo.group(1)
        parts = full.split('.')
        if full.startswith('CCLib.backend.'):
            b = parts[-1]
            if b == 'CleanupLabelsproof' and m != 'CleanupLabelsproof' and not m.startswith(('Debugvar', 'Linearize', 'Tunneling', 'Stacking', 'Alloc', 'Lineartyping')):
                return f'import CCLib.{TARGET}.OpTheory\nimport CCLib.{TARGET}.Conventions'
            if b in existing or b in mods:
                return f'import CCLib.{TARGET}.{b}'
            return mo.group(0)
        if full.startswith('CCLib.aarch64.') and parts[-1] != 'Archi':
            b = A64MAP.get(parts[-1], parts[-1])
            if b.startswith('Asmgenproof'):
                b = 'Asmgenproof'
            if b == 'OpTheory':
                return f'import CCLib.{TARGET}.OpTheory\nimport CCLib.{TARGET}.OpTyping'
            return f'import CCLib.{TARGET}.{b}'
        return mo.group(0)
    s = re.sub(r'^import (\S+)', imp, s, flags=re.M)
    lines = s.split('\n')
    seen = set()
    out = []
    for l in lines:
        if l.startswith('import '):
            if l in seen:
                continue
            seen.add(l)
        out.append(l)
    s = '\n'.join(out)
    s = s.replace('\nnamespace CC\n', f'\nnamespace CC\nnamespace {NS}\n', 1)
    i = s.rindex('\nend CC')
    s = s[:i] + f'\nend {NS}' + s[i:]
    shared_hit = False
    for X in ['Positive', 'PTree', 'ZTree', 'Mem', 'Integers.Int64']:
        pat = r'\nnamespace ' + re.escape(X) + r'\n.*?\nend ' + re.escape(X) + r'\n'
        if re.search(pat, s, flags=re.S):
            s = re.sub(pat, '\n', s, flags=re.S)
            shared_hit = True
    if 'section OpPreserved' in s:
        s = re.sub(r'\nsection OpPreserved\n.*?\nend OpPreserved\n', '\n', s, flags=re.S)
        s = re.sub(r'^(import [^\n]*\n)(?!import)', lambda mo: mo.group(1) + f'import CCLib.{TARGET}.OpTheory\n', s, count=1, flags=re.M)
    s = re.sub(r'\nnamespace Op\n.*?\nend Op\n', '\n', s, flags=re.S)
    if shared_hit:
        s = re.sub(r'^(import [^\n]*\n)(?!import)', lambda mo: mo.group(1) + f'import CCLib.backend.{m}\n', s, count=1, flags=re.M)
    if '_root_.CC.' in s:
        s = re.sub(r'\ntheorem _root_\.CC\.[^\n]*\n(?:[ \t]+[^\n]*\n)*', '\n', s)
        s = re.sub(r'^(import [^\n]*\n)(?!import)', lambda mo: mo.group(1) + f'import CCLib.backend.{m}\n', s, count=1, flags=re.M)
    s = s.replace('CC.Inlining.', f'CC.{NS}.Inlining.')
    if STRIP.match(m):
        s = strip_abi(s, m)
    else:
        s = rename_abi(s)
    s = fix_refs(s, m)
    s = re.sub(r'^(namespace|end|open)( .*?)Bounds win64', r'\1\2Bounds', s, flags=re.M)
    if m == 'Bounds':
        s = bounds_fix(s)
    s = fix_recursive(s)
    s = re.sub(r'^/-\n', f'/-\n  [{NAME} instance of `CCLib/backend/{m}.lean`: the same development, in\n  namespace `CC.{NS}`, over the {NAME} operators, registers and conventions.]\n\n', s, count=1)
    return s


DECL = r'\n(?=(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:def|theorem|lemma|inductive|structure|abbrev) )'
DHEAD = r'(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(def|theorem|lemma|inductive|structure|abbrev) (\S+)'
# functions whose `win64` is implicit (inferred from a `Bounds win64` argument)
EXCL = {'MregWithinBounds', 'SlotWithinBounds', 'sizeCalleeSaveArea', 'sizeCalleeSaveArea_incr',
        'sizeCalleeSaveAreaRec_incr', 'makeEnv', 'FrameEnv', 'Bounds'}
W = r'(?<![\w.])win64(?![\w])'


def head(d, kind):
    # the part of a declaration that decides whether it takes `win64`: the
    # statement of a theorem, the whole text of a definition
    if kind in ('theorem', 'lemma'):
        cut = [k for k in (d.find(':='), d.find('\n  |')) if k >= 0]
        return d[:min(cut)] if cut else d
    k = d.find('\n\n')
    return d if k < 0 else d[:k]


def new_w64(m, s):
    b = open(f'CCLib/backend/{m}.lean').read()
    bd = {}
    for d in re.split(DECL, b):
        mo = re.match(DHEAD, d)
        if mo:
            bd[mo.group(2)] = head(d, mo.group(1))
    res = set()
    # section variables whose type mentions `win64`
    wvars = set()
    for vb in re.finditer(r'^variable[^\n]*(?:\n[ \t]+[^\n]*)*', s, flags=re.M):
        for g in re.finditer(r'\((\w+)\s*:((?:[^()]|\((?:[^()]|\([^()]*\))*\))*)\)', vb.group(0)):
            if re.search(W, g.group(2)):
                wvars.add(g.group(1))
    chunks = re.split(DECL, s)
    active = set()
    for ci, d in enumerate(chunks):
        prev = chunks[ci - 1] if ci > 0 else ''
        tail = prev[prev.rfind('\n', 0, max(0, len(prev) - 1)) + 1:] if prev else ''
        # `include X in` / `omit X in` just before this declaration
        local_inc, local_om = set(), set()
        for mo2 in re.finditer(r'^(include|omit) ([^\n]*) in\s*(?:/--(?:.|\n)*?-/\s*)?$', prev[-400:], flags=re.M):
            if prev.rstrip().endswith(mo2.group(0).rstrip()):
                (local_inc if mo2.group(1) == 'include' else local_om).update(mo2.group(2).split())
        mo = re.match(DHEAD, d)
        before = '\n'.join(chunks[:ci])
        lastv = [v.group(0) for v in re.finditer(r'^variable[^\n]*win64[^\n]*$', before, flags=re.M)]
        implicit = bool(lastv) and '{win64' in lastv[-1]
        if mo and not implicit and mo.group(1) in ('theorem', 'lemma') and ((active | local_inc) - local_om) & wvars:
            n = mo.group(2)
            if n not in EXCL and n in bd and not re.search(r'(?<![\w.])abi(?![\w])', bd[n]) \
                    and '{win64' not in head(d, 'theorem'):
                res.add(n.split('.')[-1])
        # section-wide `include` / `end` inside this chunk (after its declaration)
        for mo2 in re.finditer(r'^include ([^\n]*?)\s*$', d, flags=re.M):
            if not mo2.group(1).endswith(' in') and mo2.group(1) != 'in':
                active.update(mo2.group(1).split())
        for mo2 in re.finditer(r'^omit ([^\n]*?)\s*$', d, flags=re.M):
            if not mo2.group(1).endswith(' in'):
                active.difference_update(mo2.group(1).split())
        if re.search(r'^end \w+', d, flags=re.M):
            active = set()
    for d in chunks:
        mo = re.match(DHEAD, d)
        if not mo:
            continue
        kind, n = mo.group(1), mo.group(2)
        if n in EXCL or n not in bd or re.search(r'(?<![\w.])abi(?![\w])', bd[n]):
            continue
        hd = head(d, kind)
        if '{win64' in hd:
            continue
        if re.search(W, hd):
            res.add(n.split('.')[-1])
    return res


BASE = list(W64FUNS)
NEWBY = {m: set() for m in mods}


def deps(m, seen=None):
    # modules of `mods` imported (transitively) by `m`, including `m`
    if seen is None:
        seen = set()
    if m in seen:
        return seen
    seen.add(m)
    for mo in re.finditer(r'^import CCLib\.backend\.(\w+)', open(f'CCLib/backend/{m}.lean').read(), flags=re.M):
        if mo.group(1) in NEWBY:
            deps(mo.group(1), seen)
    return seen


DEPS = {m: deps(m) for m in mods}


def gen_scoped(m):
    global W64FUNS
    W64FUNS = BASE + sorted(set().union(*[NEWBY[d] for d in DEPS[m]]))
    return gen(m)


while True:
    outs = {m: gen_scoped(m) for m in mods}
    changed = False
    for m in mods:
        new = new_w64(m, outs[m]) - set(BASE) - NEWBY[m]
        if new:
            print('adding', m, sorted(new))
            NEWBY[m] |= new
            changed = True
    if not changed:
        break
# files adjusted by hand after generation (regenerated for the analysis only)
KEEP = set(os.environ.get('KEEP', '').split(','))
for m in mods:
    if m in KEEP:
        continue
    open(f'{tdir}/{m}.lean', 'w').write(outs[m])
    print('wrote', f'{tdir}/{m}.lean')
