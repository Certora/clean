import re,os,sys,glob
# usage (from anywhere): python3 instantiate_riscv_backend.py riscV Mod1 Mod2 ...
# copies CCLib/backend/ModX.lean to CCLib/<target>/ModX.lean, re-targeting it.
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
TARGET=sys.argv[1]   # riscV
NS={'riscV':'RiscV','x86':'X86'}[TARGET]
NAME={'riscV':'RISC-V','x86':'x86-64'}[TARGET]
mods=sys.argv[2:]
tdir=f'CCLib/{TARGET}'
existing=set(os.path.basename(f)[:-5] for f in glob.glob(f'{tdir}/*.lean'))
A64MAP={'riscV':{'OpLessdef':'OpInject','OpTyping':'OpTheory','ValueAOpproof':'ValueAOp','NeedOpProof':'NeedOp',
        'ConstpropOpproof2':'ConstpropOpproof','Conventions1':'Conventions','SelectOpproof3':'SelectOpproof4'},
        'x86':{'OpLessdef':'OpInject','ValueAOpproof':'ValueAOp','NeedOpProof':'NeedOp','Conventions1':'Conventions'}}[TARGET]
def strip_abi(s):
    # shared ValueDomain functions still take the aarch64 ABI; `.Apple` needs no
    # parameter normalisation, exactly like RISC-V and x86-64
    s=s.replace('einitRegs abi','einitRegs .Apple')
    s=s.replace('have EM := ematch_init (bc := bc) abi f.fn_params vl f.fn_sig.sig_args ht hv',
      'have EM : Ematch bc (initRegs vl f.fn_params)\n      (einitRegs .Apple f.fn_params f.fn_sig.sig_args) := by\n    rw [initRegs_eq_shared]; exact ematch_init (bc := bc) .Apple f.fn_params vl f.fn_sig.sig_args ht hv')
    if m=='ValueAnalysisSoundBasic':
        s=s.replace('/-! ## Properties of the dataflow solution -/','''omit o in
/-- The {NAME} `RTL.init_regs` is the same function as the shared one used by
    `ValueDomain.ematch_init`. -/
theorem initRegs_eq_shared : ∀ (vl : List Val) (rl : List Reg),
    RTL.initRegs vl rl = CC.RTL.initRegs vl rl
  | _ :: vs, _ :: rs => by simp only [RTL.initRegs, CC.RTL.initRegs, initRegs_eq_shared vs rs]
  | [], _ => rfl
  | _ :: _, [] => rfl

/-! ## Properties of the dataflow solution -/'''.replace('{NAME}',NAME))
    # binders
    s=re.sub(r'[ \t]*[\(\{]abi\s*:\s*[\w.]*AbiKind[\)\}]','',s)
    s=re.sub(r'\(abi\s*:=\s*abi\)','',s)
    s=re.sub(r'^\s*omit abi in\n','',s,flags=re.M)
    s=re.sub(r'^\s*include abi\n','',s,flags=re.M)
    s=re.sub(r'(?<=[ \t(])abi(?=[\s)\],])','',s)
    s=re.sub(r'^[ \t]*variable[ \t]*\n','',s,flags=re.M)
    return s
def fix_refs(s):
    if TARGET=='riscV':
        s=s.replace('opStrengthReduction o ','opStrengthReduction ')
    s=s.replace(f'import CCLib.{TARGET}.CombineOp\n',f'import CCLib.{TARGET}.CombineOp\nimport CCLib.{TARGET}.CSEdomain\n') if m!='CSEdomain' else s
    s=re.sub(r'(?<![\w.])evalOperation_preserved','Op.evalOperation_preserved',s)
    s=re.sub(r'(?<![\w.])evalAddressing_preserved','Op.evalAddressing_preserved',s)
    s=s.replace('CleanupLabelsproof.listNthZ_mem','CminorSel.listNthZ_mem')
    return s
for m in mods:
    src=f'CCLib/backend/{m}.lean'
    s=open(src).read()
    def imp(mo):
        full=mo.group(1)
        parts=full.split('.')
        if full.startswith('CCLib.backend.'):
            b=parts[-1]
            if b in existing or b in mods: return f'import CCLib.{TARGET}.{b}'
            if b=='CleanupLabelsproof': return f'import CCLib.{TARGET}.OpTheory\nimport CCLib.{TARGET}.Conventions'
            return mo.group(0)
        if full.startswith('CCLib.aarch64.') and parts[-1]!='Archi':
            b=A64MAP.get(parts[-1],parts[-1])
            if b.startswith('Asmgenproof'): b='Asmgenproof'
            return f'import CCLib.{TARGET}.{b}'
        return mo.group(0)
    s=re.sub(r'^import (\S+)',imp,s,flags=re.M)
    # dedupe imports
    lines=s.split('\n'); seen=set(); out=[]
    for l in lines:
        if l.startswith('import '):
            if l in seen: continue
            seen.add(l)
        out.append(l)
    s='\n'.join(out)
    s=s.replace('\nnamespace CC\n',f'\nnamespace CC\nnamespace {NS}\n',1)
    i=s.rindex('\nend CC')
    s=s[:i]+f'\nend {NS}'+s[i:]
    s=s.replace('_root_.CC.Positive','_root_.CC.Positive')
    shared_hit=False
    for X in ['Positive','PTree','ZTree','Mem','Integers.Int64']:
        pat=r'\nnamespace '+re.escape(X)+r'\n.*?\nend '+re.escape(X)+r'\n'
        if re.search(pat,s,flags=re.S):
            s=re.sub(pat,'\n',s,flags=re.S); shared_hit=True
    if 'section OpPreserved' in s:
        s=re.sub(r'\nsection OpPreserved\n.*?\nend OpPreserved\n','\n',s,flags=re.S)
        s=re.sub(r'^(import [^\n]*\n)(?!import)',lambda mo: mo.group(1)+f'import CCLib.{TARGET}.OpTheory\n',s,count=1,flags=re.M)
    if TARGET in ('riscV','x86'):
        s=re.sub(r'\nnamespace Op\n.*?\nend Op\n','\n',s,flags=re.S)
    if shared_hit:
        s=re.sub(r'^(import [^\n]*\n)(?!import)',lambda mo: mo.group(1)+f'import CCLib.backend.{m}\n',s,count=1,flags=re.M)
    if '_root_.CC.' in s:
        s=re.sub(r'\ntheorem _root_\.CC\.[^\n]*\n(?:[ \t]+[^\n]*\n)*','\n',s)
        s=s.replace('\nnamespace CC\n',f'\nnamespace CC\n',1)
        s=re.sub(r'^(import [^\n]*\n)(?!import)',lambda mo: mo.group(1)+f'import CCLib.backend.{m}\n',s,count=1,flags=re.M)
    s=s.replace('CC.Inlining.',f'CC.{NS}.Inlining.')
    if TARGET in ('riscV','x86'):
        s=strip_abi(s)
        s=fix_refs(s)
    # header note
    s=re.sub(r'^/-\n', f'/-\n  [{NAME} instance of `CCLib/backend/{m}.lean`: the same development, in\n  namespace `CC.{NS}`, over the {NAME} operators, registers and conventions.]\n\n', s, count=1)
    open(f'{tdir}/{m}.lean','w').write(s)
    print('wrote',f'{tdir}/{m}.lean')
