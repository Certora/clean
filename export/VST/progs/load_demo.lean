import Clightdefs
open CC

namespace Load_demo

namespace Info
  def version : String := "3.17"
  def build_number : String := ""
  def build_tag : String := ""
  def build_branch : String := ""
  def arch : String := "aarch64"
  def model : String := "default"
  def abi : String := "standard"
  def bitsize : Nat := 64
  def big_endian : Bool := false
  def source_file : String := "load_demo.c"
  def normalized : Bool := true
end Info

def ___builtin_ais_annot : Ident := identOfString "__builtin_ais_annot"
def ___builtin_annot : Ident := identOfString "__builtin_annot"
def ___builtin_annot_intval : Ident := identOfString "__builtin_annot_intval"
def ___builtin_bswap : Ident := identOfString "__builtin_bswap"
def ___builtin_bswap16 : Ident := identOfString "__builtin_bswap16"
def ___builtin_bswap32 : Ident := identOfString "__builtin_bswap32"
def ___builtin_bswap64 : Ident := identOfString "__builtin_bswap64"
def ___builtin_cls : Ident := identOfString "__builtin_cls"
def ___builtin_clsl : Ident := identOfString "__builtin_clsl"
def ___builtin_clsll : Ident := identOfString "__builtin_clsll"
def ___builtin_clz : Ident := identOfString "__builtin_clz"
def ___builtin_clzl : Ident := identOfString "__builtin_clzl"
def ___builtin_clzll : Ident := identOfString "__builtin_clzll"
def ___builtin_ctz : Ident := identOfString "__builtin_ctz"
def ___builtin_ctzl : Ident := identOfString "__builtin_ctzl"
def ___builtin_ctzll : Ident := identOfString "__builtin_ctzll"
def ___builtin_debug : Ident := identOfString "__builtin_debug"
def ___builtin_expect : Ident := identOfString "__builtin_expect"
def ___builtin_fabs : Ident := identOfString "__builtin_fabs"
def ___builtin_fabsf : Ident := identOfString "__builtin_fabsf"
def ___builtin_fmadd : Ident := identOfString "__builtin_fmadd"
def ___builtin_fmax : Ident := identOfString "__builtin_fmax"
def ___builtin_fmin : Ident := identOfString "__builtin_fmin"
def ___builtin_fmsub : Ident := identOfString "__builtin_fmsub"
def ___builtin_fnmadd : Ident := identOfString "__builtin_fnmadd"
def ___builtin_fnmsub : Ident := identOfString "__builtin_fnmsub"
def ___builtin_fsqrt : Ident := identOfString "__builtin_fsqrt"
def ___builtin_membar : Ident := identOfString "__builtin_membar"
def ___builtin_memcpy_aligned : Ident := identOfString "__builtin_memcpy_aligned"
def ___builtin_sel : Ident := identOfString "__builtin_sel"
def ___builtin_sqrt : Ident := identOfString "__builtin_sqrt"
def ___builtin_unreachable : Ident := identOfString "__builtin_unreachable"
def ___builtin_va_arg : Ident := identOfString "__builtin_va_arg"
def ___builtin_va_copy : Ident := identOfString "__builtin_va_copy"
def ___builtin_va_end : Ident := identOfString "__builtin_va_end"
def ___builtin_va_start : Ident := identOfString "__builtin_va_start"
def ___compcert_i64_dtos : Ident := identOfString "__compcert_i64_dtos"
def ___compcert_i64_dtou : Ident := identOfString "__compcert_i64_dtou"
def ___compcert_i64_sar : Ident := identOfString "__compcert_i64_sar"
def ___compcert_i64_sdiv : Ident := identOfString "__compcert_i64_sdiv"
def ___compcert_i64_shl : Ident := identOfString "__compcert_i64_shl"
def ___compcert_i64_shr : Ident := identOfString "__compcert_i64_shr"
def ___compcert_i64_smod : Ident := identOfString "__compcert_i64_smod"
def ___compcert_i64_smulh : Ident := identOfString "__compcert_i64_smulh"
def ___compcert_i64_stod : Ident := identOfString "__compcert_i64_stod"
def ___compcert_i64_stof : Ident := identOfString "__compcert_i64_stof"
def ___compcert_i64_udiv : Ident := identOfString "__compcert_i64_udiv"
def ___compcert_i64_umod : Ident := identOfString "__compcert_i64_umod"
def ___compcert_i64_umulh : Ident := identOfString "__compcert_i64_umulh"
def ___compcert_i64_utod : Ident := identOfString "__compcert_i64_utod"
def ___compcert_i64_utof : Ident := identOfString "__compcert_i64_utof"
def ___compcert_va_composite : Ident := identOfString "__compcert_va_composite"
def ___compcert_va_float64 : Ident := identOfString "__compcert_va_float64"
def ___compcert_va_int32 : Ident := identOfString "__compcert_va_int32"
def ___compcert_va_int64 : Ident := identOfString "__compcert_va_int64"
def _b0 : Ident := identOfString "b0"
def _b1 : Ident := identOfString "b1"
def _b2 : Ident := identOfString "b2"
def _b3 : Ident := identOfString "b3"
def _fiddle : Ident := identOfString "fiddle"
def _fst : Ident := identOfString "fst"
def _get22 : Ident := identOfString "get22"
def _get_little_endian : Ident := identOfString "get_little_endian"
def _i : Ident := identOfString "i"
def _input : Ident := identOfString "input"
def _int_pair : Ident := identOfString "int_pair"
def _left : Ident := identOfString "left"
def _main : Ident := identOfString "main"
def _obj : Ident := identOfString "obj"
def _onetwo : Ident := identOfString "onetwo"
def _p : Ident := identOfString "p"
def _pair_pair : Ident := identOfString "pair_pair"
def _pp : Ident := identOfString "pp"
def _pps : Ident := identOfString "pps"
def _r : Ident := identOfString "r"
def _res : Ident := identOfString "res"
def _res1 : Ident := identOfString "res1"
def _res2 : Ident := identOfString "res2"
def _res3 : Ident := identOfString "res3"
def _right : Ident := identOfString "right"
def _size : Ident := identOfString "size"
def _snd : Ident := identOfString "snd"
def _sum : Ident := identOfString "sum"
def _tagword : Ident := identOfString "tagword"
def _threefour : Ident := identOfString "threefour"
def _v : Ident := identOfString "v"
def _t'1 : Ident := (Positive.ofNat 128)
def _t'2 : Ident := (Positive.ofNat 129)
def _t'3 : Ident := (Positive.ofNat 130)

def f_get22 : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_pps, (tptr (Ty.Tstruct _pair_pair noattr))), (_i, tint)],
  fn_vars := [],
  fn_temps := [(_p, (tptr (Ty.Tstruct _int_pair noattr))), (_res, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _p
    (Expr.Eaddrof
      (Expr.Efield
        (Expr.Ederef
          (Expr.Ebinop Binop.Oadd
            (Expr.Etempvar _pps (tptr (Ty.Tstruct _pair_pair noattr)))
            (Expr.Etempvar _i tint) (tptr (Ty.Tstruct _pair_pair noattr)))
          (Ty.Tstruct _pair_pair noattr)) _right
        (Ty.Tstruct _int_pair noattr)) (tptr (Ty.Tstruct _int_pair noattr))))
  (Stmt.Ssequence
    (Stmt.Sset _res
      (Expr.Efield
        (Expr.Ederef (Expr.Etempvar _p (tptr (Ty.Tstruct _int_pair noattr)))
          (Ty.Tstruct _int_pair noattr)) _snd tint))
    (Stmt.Sreturn (some (Expr.Etempvar _res tint)))))
}

def f_fiddle : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [(_p, (tptr tuint))],
  fn_vars := [],
  fn_temps := [(_sum, tuint), (_size, tuint), (_i, tuint), (_tagword, tuint),
               (_r, tuint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Sset _tagword
    (Expr.Ederef
      (Expr.Ebinop Binop.Oadd (Expr.Etempvar _p (tptr tuint))
        (Expr.Eunop Unop.Oneg (Expr.Econst_int (Integers.Int.repr 1) tint)
          tint) (tptr tuint)) tuint))
  (Stmt.Ssequence
    (Stmt.Sset _sum
      (Expr.Ebinop Binop.Oand (Expr.Etempvar _tagword tuint)
        (Expr.Econst_int (Integers.Int.repr 255) tint) tuint))
    (Stmt.Ssequence
      (Stmt.Sset _size
        (Expr.Ebinop Binop.Oshr (Expr.Etempvar _tagword tuint)
          (Expr.Econst_int (Integers.Int.repr 10) tint) tuint))
      (Stmt.Ssequence
        (Stmt.Ssequence
          (Stmt.Sset _i (Expr.Econst_int (Integers.Int.repr 0) tint))
          (Stmt.Sloop
            (Stmt.Ssequence
              (Stmt.Sifthenelse (Expr.Ebinop Binop.Olt
                                  (Expr.Etempvar _i tuint)
                                  (Expr.Etempvar _size tuint) tint)
                Stmt.Sskip
                Stmt.Sbreak)
              (Stmt.Ssequence
                (Stmt.Sset _r
                  (Expr.Ederef
                    (Expr.Ebinop Binop.Oadd (Expr.Etempvar _p (tptr tuint))
                      (Expr.Etempvar _i tuint) (tptr tuint)) tuint))
                (Stmt.Sset _sum
                  (Expr.Ebinop Binop.Oadd (Expr.Etempvar _sum tuint)
                    (Expr.Etempvar _r tuint) tuint))))
            (Stmt.Sset _i
              (Expr.Ebinop Binop.Oadd (Expr.Etempvar _i tuint)
                (Expr.Econst_int (Integers.Int.repr 1) tint) tuint))))
        (Stmt.Sreturn (some (Expr.Etempvar _sum tuint)))))))
}

def f_get_little_endian : Function := {
  fn_return := tuint,
  fn_callconv := cc_default,
  fn_params := [(_input, (tptr tuchar))],
  fn_vars := [],
  fn_temps := [(_b0, tuint), (_b1, tuint), (_b2, tuint), (_b3, tuint),
               (_t'2, tuchar), (_t'1, tuchar)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Sset _t'1
      (Expr.Ederef
        (Expr.Ebinop Binop.Oadd (Expr.Etempvar _input (tptr tuchar))
          (Expr.Econst_int (Integers.Int.repr 0) tint) (tptr tuchar)) tuchar))
    (Stmt.Sset _b0 (Expr.Ecast (Expr.Etempvar _t'1 tuchar) tuint)))
  (Stmt.Ssequence
    (Stmt.Ssequence
      (Stmt.Sset _t'2
        (Expr.Ederef
          (Expr.Ebinop Binop.Oadd (Expr.Etempvar _input (tptr tuchar))
            (Expr.Econst_int (Integers.Int.repr 1) tint) (tptr tuchar))
          tuchar))
      (Stmt.Sset _b1 (Expr.Ecast (Expr.Etempvar _t'2 tuchar) tuint)))
    (Stmt.Ssequence
      (Stmt.Sset _b2
        (Expr.Ederef
          (Expr.Ebinop Binop.Oadd (Expr.Etempvar _input (tptr tuchar))
            (Expr.Econst_int (Integers.Int.repr 2) tint) (tptr tuchar))
          tuchar))
      (Stmt.Ssequence
        (Stmt.Sset _b3
          (Expr.Ederef
            (Expr.Ebinop Binop.Oadd (Expr.Etempvar _input (tptr tuchar))
              (Expr.Econst_int (Integers.Int.repr 3) tint) (tptr tuchar))
            tuchar))
        (Stmt.Sreturn (some (Expr.Ebinop Binop.Oor
                              (Expr.Ebinop Binop.Oor
                                (Expr.Ebinop Binop.Oor
                                  (Expr.Etempvar _b0 tuint)
                                  (Expr.Ebinop Binop.Oshl
                                    (Expr.Etempvar _b1 tuint)
                                    (Expr.Econst_int (Integers.Int.repr 8) tint)
                                    tuint) tuint)
                                (Expr.Ebinop Binop.Oshl
                                  (Expr.Etempvar _b2 tuint)
                                  (Expr.Econst_int (Integers.Int.repr 16) tint)
                                  tuint) tuint)
                              (Expr.Ebinop Binop.Oshl
                                (Expr.Etempvar _b3 tuint)
                                (Expr.Econst_int (Integers.Int.repr 24) tint)
                                tuint) tuint)))))))
}

def f_main : Function := {
  fn_return := tint,
  fn_callconv := cc_default,
  fn_params := [],
  fn_vars := [(_onetwo, (Ty.Tstruct _int_pair noattr)),
              (_threefour, (Ty.Tstruct _int_pair noattr)),
              (_pp, (Ty.Tstruct _pair_pair noattr)),
              (_pps, (tarray (Ty.Tstruct _pair_pair noattr) 1)),
              (_obj, (tarray tuint 3)), (_v, (tarray tuchar 4))],
  fn_temps := [(_p, (tptr tuint)), (_res1, tint), (_res2, tint),
               (_res3, tuint), (_t'3, tuint), (_t'2, tint), (_t'1, tint)],
  fn_body :=
(Stmt.Ssequence
  (Stmt.Ssequence
    (Stmt.Sassign
      (Expr.Efield (Expr.Evar _onetwo (Ty.Tstruct _int_pair noattr)) _fst
        tint) (Expr.Econst_int (Integers.Int.repr 1) tint))
    (Stmt.Ssequence
      (Stmt.Sassign
        (Expr.Efield (Expr.Evar _onetwo (Ty.Tstruct _int_pair noattr)) _snd
          tint) (Expr.Econst_int (Integers.Int.repr 2) tint))
      (Stmt.Ssequence
        (Stmt.Sassign
          (Expr.Efield (Expr.Evar _threefour (Ty.Tstruct _int_pair noattr))
            _fst tint) (Expr.Econst_int (Integers.Int.repr 3) tint))
        (Stmt.Ssequence
          (Stmt.Sassign
            (Expr.Efield (Expr.Evar _threefour (Ty.Tstruct _int_pair noattr))
              _snd tint) (Expr.Econst_int (Integers.Int.repr 4) tint))
          (Stmt.Ssequence
            (Stmt.Sassign
              (Expr.Efield (Expr.Evar _pp (Ty.Tstruct _pair_pair noattr))
                _left (Ty.Tstruct _int_pair noattr))
              (Expr.Evar _onetwo (Ty.Tstruct _int_pair noattr)))
            (Stmt.Ssequence
              (Stmt.Sassign
                (Expr.Efield (Expr.Evar _pp (Ty.Tstruct _pair_pair noattr))
                  _right (Ty.Tstruct _int_pair noattr))
                (Expr.Evar _threefour (Ty.Tstruct _int_pair noattr)))
              (Stmt.Ssequence
                (Stmt.Sassign
                  (Expr.Ederef
                    (Expr.Ebinop Binop.Oadd
                      (Expr.Evar _pps (tarray (Ty.Tstruct _pair_pair noattr) 1))
                      (Expr.Econst_int (Integers.Int.repr 0) tint)
                      (tptr (Ty.Tstruct _pair_pair noattr)))
                    (Ty.Tstruct _pair_pair noattr))
                  (Expr.Evar _pp (Ty.Tstruct _pair_pair noattr)))
                (Stmt.Ssequence
                  (Stmt.Sassign
                    (Expr.Ederef
                      (Expr.Ebinop Binop.Oadd
                        (Expr.Evar _obj (tarray tuint 3))
                        (Expr.Econst_int (Integers.Int.repr 0) tint)
                        (tptr tuint)) tuint)
                    (Expr.Ebinop Binop.Oshl
                      (Expr.Econst_int (Integers.Int.repr 2) tint)
                      (Expr.Econst_int (Integers.Int.repr 10) tint) tint))
                  (Stmt.Ssequence
                    (Stmt.Sassign
                      (Expr.Ederef
                        (Expr.Ebinop Binop.Oadd
                          (Expr.Evar _obj (tarray tuint 3))
                          (Expr.Econst_int (Integers.Int.repr 1) tint)
                          (tptr tuint)) tuint)
                      (Expr.Econst_int (Integers.Int.repr 11) tint))
                    (Stmt.Ssequence
                      (Stmt.Sassign
                        (Expr.Ederef
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Evar _obj (tarray tuint 3))
                            (Expr.Econst_int (Integers.Int.repr 2) tint)
                            (tptr tuint)) tuint)
                        (Expr.Econst_int (Integers.Int.repr 12) tint))
                      (Stmt.Ssequence
                        (Stmt.Sset _p
                          (Expr.Ebinop Binop.Oadd
                            (Expr.Evar _obj (tarray tuint 3))
                            (Expr.Econst_int (Integers.Int.repr 1) tint)
                            (tptr tuint)))
                        (Stmt.Ssequence
                          (Stmt.Sassign
                            (Expr.Ederef
                              (Expr.Ebinop Binop.Oadd
                                (Expr.Evar _v (tarray tuchar 4))
                                (Expr.Econst_int (Integers.Int.repr 0) tint)
                                (tptr tuchar)) tuchar)
                            (Expr.Econst_int (Integers.Int.repr 10) tint))
                          (Stmt.Ssequence
                            (Stmt.Sassign
                              (Expr.Ederef
                                (Expr.Ebinop Binop.Oadd
                                  (Expr.Evar _v (tarray tuchar 4))
                                  (Expr.Econst_int (Integers.Int.repr 1) tint)
                                  (tptr tuchar)) tuchar)
                              (Expr.Econst_int (Integers.Int.repr 20) tint))
                            (Stmt.Ssequence
                              (Stmt.Sassign
                                (Expr.Ederef
                                  (Expr.Ebinop Binop.Oadd
                                    (Expr.Evar _v (tarray tuchar 4))
                                    (Expr.Econst_int (Integers.Int.repr 2) tint)
                                    (tptr tuchar)) tuchar)
                                (Expr.Econst_int (Integers.Int.repr 30) tint))
                              (Stmt.Ssequence
                                (Stmt.Sassign
                                  (Expr.Ederef
                                    (Expr.Ebinop Binop.Oadd
                                      (Expr.Evar _v (tarray tuchar 4))
                                      (Expr.Econst_int (Integers.Int.repr 3) tint)
                                      (tptr tuchar)) tuchar)
                                  (Expr.Econst_int (Integers.Int.repr 40) tint))
                                (Stmt.Ssequence
                                  (Stmt.Ssequence
                                    (Stmt.Scall (some _t'1)
                                      (Expr.Evar _get22 (Ty.Tfunction
                                                          [(tptr (Ty.Tstruct _pair_pair noattr)),
                                                           tint] tint
                                                          cc_default))
                                      [(Expr.Evar _pps (tarray (Ty.Tstruct _pair_pair noattr) 1)),
                                       (Expr.Econst_int (Integers.Int.repr 0) tint)])
                                    (Stmt.Sset _res1
                                      (Expr.Etempvar _t'1 tint)))
                                  (Stmt.Ssequence
                                    (Stmt.Ssequence
                                      (Stmt.Scall (some _t'2)
                                        (Expr.Evar _fiddle (Ty.Tfunction
                                                             [(tptr tuint)]
                                                             tint cc_default))
                                        [(Expr.Etempvar _p (tptr tuint))])
                                      (Stmt.Sset _res2
                                        (Expr.Etempvar _t'2 tint)))
                                    (Stmt.Ssequence
                                      (Stmt.Ssequence
                                        (Stmt.Scall (some _t'3)
                                          (Expr.Evar _get_little_endian 
                                          (Ty.Tfunction [(tptr tuchar)] tuint
                                            cc_default))
                                          [(Expr.Evar _v (tarray tuchar 4))])
                                        (Stmt.Sset _res3
                                          (Expr.Etempvar _t'3 tuint)))
                                      (Stmt.Sreturn (some (Expr.Ebinop Binop.Oadd
                                                            (Expr.Ebinop Binop.Oadd
                                                              (Expr.Etempvar _res1 tint)
                                                              (Expr.Etempvar _res2 tint)
                                                              tint)
                                                            (Expr.Ebinop Binop.Oshr
                                                              (Expr.Etempvar _res3 tuint)
                                                              (Expr.Econst_int (Integers.Int.repr 24) tint)
                                                              tuint) tuint)))))))))))))))))))))
  (Stmt.Sreturn (some (Expr.Econst_int (Integers.Int.repr 0) tint))))
}

def composites : List CompositeDef :=
[(CompositeDef.Composite _int_pair SU.Struct
   [(Member.Member_plain _fst tint), (Member.Member_plain _snd tint)]
   noattr),
 (CompositeDef.Composite _pair_pair SU.Struct
   [(Member.Member_plain _left (Ty.Tstruct _int_pair noattr)),
    (Member.Member_plain _right (Ty.Tstruct _int_pair noattr))]
   noattr)]

def global_definitions : List (Ident × GlobDef FunDef Ty) :=
[(___compcert_va_int32,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_va_int32"
                                   (mksignature [XType.Xptr] XType.Xint
                                     cc_default)) [(tptr tvoid)] tuint
     cc_default)),
 (___compcert_va_int64,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_va_int64"
                                   (mksignature [XType.Xptr] XType.Xlong
                                     cc_default)) [(tptr tvoid)] tulong
     cc_default)),
 (___compcert_va_float64,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_va_float64"
                                   (mksignature [XType.Xptr] XType.Xfloat
                                     cc_default)) [(tptr tvoid)] tdouble
     cc_default)),
 (___compcert_va_composite,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_va_composite"
                                   (mksignature [XType.Xptr, XType.Xlong]
                                     XType.Xptr cc_default))
     [(tptr tvoid), tulong] (tptr tvoid) cc_default)),
 (___compcert_i64_dtos,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_dtos"
                                   (mksignature [XType.Xfloat] XType.Xlong
                                     cc_default)) [tdouble] tlong
     cc_default)),
 (___compcert_i64_dtou,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_dtou"
                                   (mksignature [XType.Xfloat] XType.Xlong
                                     cc_default)) [tdouble] tulong
     cc_default)),
 (___compcert_i64_stod,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_stod"
                                   (mksignature [XType.Xlong] XType.Xfloat
                                     cc_default)) [tlong] tdouble
     cc_default)),
 (___compcert_i64_utod,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_utod"
                                   (mksignature [XType.Xlong] XType.Xfloat
                                     cc_default)) [tulong] tdouble
     cc_default)),
 (___compcert_i64_stof,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_stof"
                                   (mksignature [XType.Xlong] XType.Xsingle
                                     cc_default)) [tlong] tfloat cc_default)),
 (___compcert_i64_utof,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_utof"
                                   (mksignature [XType.Xlong] XType.Xsingle
                                     cc_default)) [tulong] tfloat
     cc_default)),
 (___compcert_i64_sdiv,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_sdiv"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default)) [tlong, tlong]
     tlong cc_default)),
 (___compcert_i64_udiv,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_udiv"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default))
     [tulong, tulong] tulong cc_default)),
 (___compcert_i64_smod,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_smod"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default)) [tlong, tlong]
     tlong cc_default)),
 (___compcert_i64_umod,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_umod"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default))
     [tulong, tulong] tulong cc_default)),
 (___compcert_i64_shl,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_shl"
                                   (mksignature [XType.Xlong, XType.Xint]
                                     XType.Xlong cc_default)) [tlong, tint]
     tlong cc_default)),
 (___compcert_i64_shr,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_shr"
                                   (mksignature [XType.Xlong, XType.Xint]
                                     XType.Xlong cc_default)) [tulong, tint]
     tulong cc_default)),
 (___compcert_i64_sar,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_sar"
                                   (mksignature [XType.Xlong, XType.Xint]
                                     XType.Xlong cc_default)) [tlong, tint]
     tlong cc_default)),
 (___compcert_i64_smulh,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_smulh"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default)) [tlong, tlong]
     tlong cc_default)),
 (___compcert_i64_umulh,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_runtime "__compcert_i64_umulh"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default))
     [tulong, tulong] tulong cc_default)),
 (___builtin_ais_annot,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_ais_annot"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false }))
     [(tptr tuchar)] tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___builtin_bswap64,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_bswap64"
                                   (mksignature [XType.Xlong] XType.Xlong
                                     cc_default)) [tulong] tulong
     cc_default)),
 (___builtin_bswap,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_bswap"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tuint] tuint cc_default)),
 (___builtin_bswap32,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_bswap32"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tuint] tuint cc_default)),
 (___builtin_bswap16,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_bswap16"
                                   (mksignature [XType.Xint16unsigned]
                                     XType.Xint16unsigned cc_default))
     [tushort] tushort cc_default)),
 (___builtin_clz,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clz"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tuint] tint cc_default)),
 (___builtin_clzl,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clzl"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tulong] tint cc_default)),
 (___builtin_clzll,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clzll"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tulong] tint cc_default)),
 (___builtin_ctz,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_ctz"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tuint] tint cc_default)),
 (___builtin_ctzl,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_ctzl"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tulong] tint cc_default)),
 (___builtin_ctzll,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_ctzll"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tulong] tint cc_default)),
 (___builtin_fabs,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fabs"
                                   (mksignature [XType.Xfloat] XType.Xfloat
                                     cc_default)) [tdouble] tdouble
     cc_default)),
 (___builtin_fabsf,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fabsf"
                                   (mksignature [XType.Xsingle] XType.Xsingle
                                     cc_default)) [tfloat] tfloat
     cc_default)),
 (___builtin_fsqrt,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fsqrt"
                                   (mksignature [XType.Xfloat] XType.Xfloat
                                     cc_default)) [tdouble] tdouble
     cc_default)),
 (___builtin_sqrt,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_sqrt"
                                   (mksignature [XType.Xfloat] XType.Xfloat
                                     cc_default)) [tdouble] tdouble
     cc_default)),
 (___builtin_memcpy_aligned,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_memcpy_aligned"
                                   (mksignature
                                     [XType.Xptr, XType.Xptr, XType.Xlong,
                                      XType.Xlong] XType.Xvoid cc_default))
     [(tptr tvoid), (tptr tvoid), tulong, tulong] tvoid cc_default)),
 (___builtin_sel,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_sel"
                                   (mksignature [XType.Xbool] XType.Xvoid
                                     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false }))
     [tbool] tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___builtin_annot,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_annot"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false }))
     [(tptr tuchar)] tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (___builtin_annot_intval,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_annot_intval"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xint cc_default))
     [(tptr tuchar), tint] tint cc_default)),
 (___builtin_membar,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_membar"
                                   (mksignature [] XType.Xvoid cc_default))
     [] tvoid cc_default)),
 (___builtin_va_start,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_va_start"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default)) [(tptr tvoid)] tvoid
     cc_default)),
 (___builtin_va_arg,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_va_arg"
                                   (mksignature [XType.Xptr, XType.Xint]
                                     XType.Xvoid cc_default))
     [(tptr tvoid), tuint] tvoid cc_default)),
 (___builtin_va_copy,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_va_copy"
                                   (mksignature [XType.Xptr, XType.Xptr]
                                     XType.Xvoid cc_default))
     [(tptr tvoid), (tptr tvoid)] tvoid cc_default)),
 (___builtin_va_end,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_va_end"
                                   (mksignature [XType.Xptr] XType.Xvoid
                                     cc_default)) [(tptr tvoid)] tvoid
     cc_default)),
 (___builtin_unreachable,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_unreachable"
                                   (mksignature [] XType.Xvoid cc_default))
     [] tvoid cc_default)),
 (___builtin_expect,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_expect"
                                   (mksignature [XType.Xlong, XType.Xlong]
                                     XType.Xlong cc_default)) [tlong, tlong]
     tlong cc_default)),
 (___builtin_cls,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_cls"
                                   (mksignature [XType.Xint] XType.Xint
                                     cc_default)) [tint] tint cc_default)),
 (___builtin_clsl,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clsl"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tlong] tint cc_default)),
 (___builtin_clsll,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_clsll"
                                   (mksignature [XType.Xlong] XType.Xint
                                     cc_default)) [tlong] tint cc_default)),
 (___builtin_fmadd,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fmadd"
                                   (mksignature
                                     [XType.Xfloat, XType.Xfloat,
                                      XType.Xfloat] XType.Xfloat cc_default))
     [tdouble, tdouble, tdouble] tdouble cc_default)),
 (___builtin_fmsub,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fmsub"
                                   (mksignature
                                     [XType.Xfloat, XType.Xfloat,
                                      XType.Xfloat] XType.Xfloat cc_default))
     [tdouble, tdouble, tdouble] tdouble cc_default)),
 (___builtin_fnmadd,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fnmadd"
                                   (mksignature
                                     [XType.Xfloat, XType.Xfloat,
                                      XType.Xfloat] XType.Xfloat cc_default))
     [tdouble, tdouble, tdouble] tdouble cc_default)),
 (___builtin_fnmsub,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fnmsub"
                                   (mksignature
                                     [XType.Xfloat, XType.Xfloat,
                                      XType.Xfloat] XType.Xfloat cc_default))
     [tdouble, tdouble, tdouble] tdouble cc_default)),
 (___builtin_fmax,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fmax"
                                   (mksignature [XType.Xfloat, XType.Xfloat]
                                     XType.Xfloat cc_default))
     [tdouble, tdouble] tdouble cc_default)),
 (___builtin_fmin,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_builtin "__builtin_fmin"
                                   (mksignature [XType.Xfloat, XType.Xfloat]
                                     XType.Xfloat cc_default))
     [tdouble, tdouble] tdouble cc_default)),
 (___builtin_debug,
   GlobDef.Gfun (FunDef.External (ExtFun.EF_external "__builtin_debug"
                                   (mksignature [XType.Xint] XType.Xvoid
                                     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false }))
     [tint] tvoid
     { cc_vararg := (some 1), cc_unproto := false, cc_structret := false })),
 (_get22, GlobDef.Gfun (FunDef.Internal f_get22)),
 (_fiddle, GlobDef.Gfun (FunDef.Internal f_fiddle)),
 (_get_little_endian, GlobDef.Gfun (FunDef.Internal f_get_little_endian)),
 (_main, GlobDef.Gfun (FunDef.Internal f_main))]

def public_idents : List Ident :=
[_main, _get_little_endian, _fiddle, _get22, ___builtin_debug,
 ___builtin_fmin, ___builtin_fmax, ___builtin_fnmsub, ___builtin_fnmadd,
 ___builtin_fmsub, ___builtin_fmadd, ___builtin_clsll, ___builtin_clsl,
 ___builtin_cls, ___builtin_expect, ___builtin_unreachable,
 ___builtin_va_end, ___builtin_va_copy, ___builtin_va_arg,
 ___builtin_va_start, ___builtin_membar, ___builtin_annot_intval,
 ___builtin_annot, ___builtin_sel, ___builtin_memcpy_aligned,
 ___builtin_sqrt, ___builtin_fsqrt, ___builtin_fabsf, ___builtin_fabs,
 ___builtin_ctzll, ___builtin_ctzl, ___builtin_ctz, ___builtin_clzll,
 ___builtin_clzl, ___builtin_clz, ___builtin_bswap16, ___builtin_bswap32,
 ___builtin_bswap, ___builtin_bswap64, ___builtin_ais_annot,
 ___compcert_i64_umulh, ___compcert_i64_smulh, ___compcert_i64_sar,
 ___compcert_i64_shr, ___compcert_i64_shl, ___compcert_i64_umod,
 ___compcert_i64_smod, ___compcert_i64_udiv, ___compcert_i64_sdiv,
 ___compcert_i64_utof, ___compcert_i64_stof, ___compcert_i64_utod,
 ___compcert_i64_stod, ___compcert_i64_dtou, ___compcert_i64_dtos,
 ___compcert_va_composite, ___compcert_va_float64, ___compcert_va_int64,
 ___compcert_va_int32]

def prog : Program :=
  mkprogram composites global_definitions public_idents _main

end Load_demo

