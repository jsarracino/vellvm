From Flocq Require Import Binary.


From Coq Require Import Reals Psatz ssrbool List.

From QuickChick Require Import Show.

From Vellvm Require Import 
    LLVMAst 
    Syntax
    Semantics
    Utilities
    DynamicValues
    Utils.MapMonadExtra
    Utils.MonadEq1Laws
    Utils.MonadReturnsLaws
    Utils.MonadExcLaws
    Semantics.Memory.Sizeof
    Theory
    Theory.Refinement
    Semantics.IntrinsicsDefinitions
    Semantics.LLVMEvents.

From ExtLib Require Import 
Structures.Monads.

From ITree Require Import 
    ITree
    Eq.Eqit.

Set Implicit Arguments.
Set Contextual Implicit.


Import ITreeNotations.


(* Fast math flags implemented in Vellvm: 

    Variant fast_math : Set :=
    Nnan 
    | Ninf 
    | Nsz 
    | Arcp 
    | Contract
    | Afn 
    | Reassoc 
    | Fast.
*)

(* Let us start looking at three fast math flags implemented 
by LifeJacket with is FP extension of Alive *)

(* 
Semantics of the flags as per the LLVM reference manual

Nnan: Allows the optimization to assume the arguments and
result are not NaN

If an argument is a NaN, or the result would be a NaN, it
produces a poison value instead.

r = f_op (a, b)

assume (!isNan(a) && !isNan(b) && !isNan(r))
ensures (isNan(a) || isNan(b) || isNan(r) ==> r = poison_value)


NInf: Allows optimizations to assume the arguments and results are not
+/- Inf.

If an argument or the result would be +/- inf, it produces poison value instead

r = f_op (a, b)
assume (!isInf(a) && !isNaN(b) && !isNaN(r))
ensures (isNaN(a) || isNaN(b) || isNaN(r) ==> r = poison_value )

Nsz : Allow optimizations to treat the sign of a zero argument or zero
result as insignificant.

assume (isZero(a_src) && isZero(a_tgt) ==> a_src =f a_tgt)

*)

Module FM (A:Vellvm.Semantics.MemoryAddress.ADDRESS)(IP:Vellvm.Semantics.MemoryAddress.INTPTR)(SIZEOF:Sizeof)  (IS : InterpreterStack) (TOP : LLVMTopLevel IS) (LLVMIO: LLVM_INTERACTIONS(A)(IP)(SIZEOF)).

Import IS.
Import SemNotations.

Module R := Refinement.Make LP LLVM.
Import R.

Module E1 := DVALUE A IP SIZEOF.

Import E1.
Module CFGT := CFGTheory IS TOP.
Import CFGT.

Module E2 := IntrinsicsDefinitions.Make A IP SIZEOF LLVMIO.
Import E2.


Section FastMath.

Definition is_nan32 (f : ll_float) : bool :=
    (Binary.is_nan _ _ f).

Definition is_nan64 (f : ll_double) : bool :=
    (Binary.is_nan _ _ f).

Definition is_zero {prec emax : Z} (f : binary_float prec emax) :=
    match f with 
    | B754_zero _   => true
    | _           => false
    end.

Definition is_zero_32 (f : ll_float) : bool :=
    @is_zero 24 128 f.

Definition is_zero_64 (f : ll_double) : bool :=
    @is_zero 53 1024 f.

(* + inf **)    
Definition is_pos_inf64 (f : ll_double) : bool :=
    match f with 
    | B754_infinity false => true
    | _                   => false
    end.

(* - inf *)
Definition is_neg_inf64 (f : ll_double) : bool :=
    match f with 
    | B754_infinity true => true
    | _                   => false
    end.

Definition is_inf64 (f : ll_double) : bool :=
    is_pos_inf64 f || is_neg_inf64 f .

Print Bfma.

Parameter fma_nan :
    forall (prec emax : Z),
    binary_float prec emax -> 
    binary_float prec emax ->
    binary_float prec emax ->
    {x : binary_float prec emax | is_nan prec emax x = true }.

Parameter bplus_nan :
    forall (prec emax : Z),
    binary_float prec emax -> 
    binary_float prec emax ->
    {x : binary_float prec emax | is_nan prec emax x = true }.

Parameter bminus_nan :
    forall (prec emax : Z),
    binary_float prec emax -> 
    binary_float prec emax ->
    {x : binary_float prec emax | is_nan prec emax x = true }.

Parameter bmult_nan :
    forall (prec emax : Z),
    binary_float prec emax -> 
    binary_float prec emax ->
    {x : binary_float prec emax | is_nan prec emax x = true }.


Parameter bdiv_nan :
    forall (prec emax : Z),
    binary_float prec emax -> 
    binary_float prec emax ->
    {x : binary_float prec emax | is_nan prec emax x = true }.

Parameter babs_nan :
    forall (prec emax : Z),
    binary_float prec emax -> 
    {x : binary_float prec emax | is_nan prec emax x = true }.    

Lemma prec_gt_0:
FLX.Prec_gt_0 53.
Proof. unfold FLX.Prec_gt_0. lia. Qed.

Lemma prec_lt_emax:
BinarySingleNaN.Prec_lt_emax 53 1024.
Proof. unfold BinarySingleNaN.Prec_lt_emax. lia. Qed.

Definition b64_fma (rnd_mode : BinarySingleNaN.mode) (v1 : ll_double) (v2 : ll_double) (v3 : ll_double) :=
    @Bfma 53 1024 prec_gt_0 prec_lt_emax (@fma_nan 53 1024) rnd_mode v1 v2 v3 .

Definition b64_plus (rnd_mode : BinarySingleNaN.mode) (v1 : ll_double) (v2 : ll_double) :=
    @Bplus 53 1024 prec_gt_0 prec_lt_emax (@bplus_nan 53 1024) rnd_mode v1 v2.

Definition b64_minus (rnd_mode : BinarySingleNaN.mode) (v1 : ll_double) (v2 : ll_double) :=
    @Bminus 53 1024 prec_gt_0 prec_lt_emax (@bminus_nan 53 1024) rnd_mode v1 v2.

Definition b64_mult (rnd_mode : BinarySingleNaN.mode) (v1 : ll_double) (v2 : ll_double) :=
    @Bmult 53 1024 prec_gt_0 prec_lt_emax (@bmult_nan 53 1024) rnd_mode v1 v2.

Definition b64_div (rnd_mode : BinarySingleNaN.mode) (v1 : ll_double) (v2 : ll_double) :=
    @Bdiv 53 1024 prec_gt_0 prec_lt_emax (@bdiv_nan 53 1024) rnd_mode v1 v2.


(* Nnan semantics *)

(* Examples from LifeJacket 


    Name: XSubX:InstructionSimplify:859
    %r = fsub nnan %x, %x
    =>
    %r = 0.0

    assumes that %x and %x are not nan. 

    assumes that %x and %x are finite. hence the result is zero.

    But, %x can be infinity.

    Flocq semantics for fsub:
    Definition Bminus m x y :=
    match x, y with
    | B754_nan, _ | _, B754_nan => B754_nan
    | B754_infinity sx, B754_infinity sy =>
        if Bool.eqb sx (negb sy) then x else B754_nan
    | B754_infinity _, _ => x
    | _, B754_infinity sy => B754_infinity (negb sy)
    | B754_zero sx, B754_zero sy =>
        if Bool.eqb sx (negb sy) then x else
        match m with mode_DN => B754_zero true | _ => B754_zero false end
    | B754_zero _, B754_finite sy my ey Hy => B754_finite (negb sy) my ey Hy
    | _, B754_zero _ => x
    | B754_finite sx mx ex Hx, B754_finite sy my ey Hy =>
        let ez := Z.min ex ey in
        binary_normalize m (Fplus_naive sx mx ex (negb sy) my ey ez)
        ez (match m with mode_DN => true | _ => false end)
    end.

    if %x = +inf, %x - %x = Nnan
    if %x = -inf, %x - %x = Nnan

    in that case, the resulting value should be a poison value, since the result is Nan

    similarly,

    Name: MulZero:InstructionSimplify:886-1
    %r = fmul nnan nsz %x, 0.0
    =>
    %r = 0.0    
    
    with nsz, it basically ignored the sign of zero and with nnan it assumes that %x is not a NaN.
    hence, the result is 0, where it ignores the sign of the resulting zero value as well.

    but if x is infinity, according to the flocq semantics, infinity * zero = NaN

    Hence, r should be a poison value

    Q: How are poison values represented in life Jacket and what does the type for a float look like in SMT-LIB?

    if 'nnan' in self.flags:
      expr = If(Or(fpIsNaN(self.v1_smt), fpIsNaN(self.v2_smt), fpIsNaN(expr)),
                getNewUndefName(), expr)

    if v1, v2 or expr is nan, then undef

    if 'ninf' in self.flags:
      expr = If(Or(fpIsInf(self.v1_smt), fpIsInf(self.v2_smt), fpIsInf(expr)),
                getNewUndefName(), expr)

    if v1, v2 or expr in inf, then undef

    LifeJacket handles the nnan and ninf flags in a similar way by modifying
    the SMT formula for the instruction on which the flag appears.
*)

(* Rough implementation of Nnan flag *)

(* Given two operands v1 and v2, a binary operation, and the fast math flag,
   let llvm perform the binop assuming nnan flag, the standard binop should 
   be equivalent to the optimized biop modulo rounding, assuming that the conditions 
   of nnan holds
*)

(*From ExtLib Require Import
     Structures.Monad
     Structures.Functor. *)

Print fast_math.
Import Monad.
Import MonadNotation.



(* Standard floating-point arithmetic in presence of Nnan flag *)
Definition double_op_nnan {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) (fm : fast_math)
: M dvalue :=
match fm with 
| Nnan => 
    if (negb (is_nan64 v1)) &&  (negb (is_nan64 v2)) then 
        let r := match fop with 
                 | FAdd => b64_plus FT_Rounding v1 v2 
                 (* FT_Rounding is set of RNE: nearest to even ties to middle *)
                 | FSub => b64_minus FT_Rounding v1 v2 
                 | FMul => b64_mult FT_Rounding v1 v2 
                 | FDiv => b64_div FT_Rounding v1 v2
                 | FRem => B754_zero 53 1024 false (* Default implementation *)
                 end
         in 
        if (is_nan64 r) then ret (DVALUE_Poison DTYPE_Double)
        else (ret (DVALUE_Double r))
     else 
        ret (DVALUE_Poison DTYPE_Double)
| _     => double_op fop v1 v2
end.

(* Equivalence between optimized llvm result r and standard floats for the nnan flag *)

(* Dummy implementation of feq *)
Definition feq (x : ll_double) (y : ll_double) := true.


Check double_op_nnan.
(* Here r is a value from LLVM opt *)
(*
Lemma nnan_fop_equiv {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) (fm : fast_math) (r : ll_double): bool :
    match fm with 
    | Nnan => let unopt_r := double_op_nnan fop v1 v2 fm in 
              match unopt_r with 
              | DVALUE_Double ur => feq ur r 
              | _                => false
              end
    | _    => true (* Default *)
    end.
Admitted.
*)


(* Standard floating-point arithmetic in presence of Ninf flag *)


Definition double_op_ninf {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) (fm :fast_math)
: M dvalue :=
match fm with 
| Ninf => 
    if (negb (is_inf64 v1)) &&  (negb (is_inf64 v2)) then 
        let r := match fop with 
                 | FAdd => b64_plus FT_Rounding v1 v2 
                 (* FT_Rounding is set of RNE: nearest to even ties to middle *)
                 | FSub => b64_minus FT_Rounding v1 v2 
                 | FMul => b64_mult FT_Rounding v1 v2 
                 | FDiv => b64_div FT_Rounding v1 v2
                 | FRem => B754_zero 53 1024 false
                 end
         in 
        if (is_inf64 r) then ret (DVALUE_Poison DTYPE_Double)
        else (ret (DVALUE_Double r))
     else 
        ret (DVALUE_Poison DTYPE_Double)
| _     => double_op fop v1 v2
end.

(* Here r is a value from LLVM opt *)
(*Lemma ninf_fop_equiv {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) (fm : list fast_math) (r : ll_double): bool :=
    match fm with 
    | Ninf => let unopt_r := double_op_ninf fop v1 v2 fm in 
              feq unopt_r
    | _    => true (* Default *)
    end.
Admitted. *)


(* nsz flag. Life Jacket implements primarily for comparison *)
Definition nsz_sem (fsrc ftgt : ll_double) (fm : fast_math) :=
    match fm with 
    | Nsz => (is_zero fsrc && is_zero ftgt) -> double_cmp FOeq fsrc ftgt = @DVALUE_I 1 Integers.one
    | _   => False
    end.

(* arcp: 

allows division to be treated as a multiplication by a reciprocal. 

Specifically, this permits a / b to be considered equivalent to  a * (1.0 / b),
and it also permits a / (b / c) to be considered equivalent to a * (c / b).

Question: is there an implicit assumption on whether b <> 0?
*)

(* Assuming both v1 and v2 are values. TODO: Implement when v2 is expr of form b / c *)
Definition double_op_arcp {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) (fm : fast_math)
: M dvalue :=
    match fm, fop with 
    | Arcp, Fdiv  =>   let denom := b64_div FT_Rounding (Bone 53 1024 prec_gt_0 prec_lt_emax) v2 in
                        ret(DVALUE_Double (b64_mult FT_Rounding v1 denom))
    | _, _           => double_op fop v1 v2
    end.

(*
Lemma arcp_equiv {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) (fm : fast_math): bool :
    match fm with 
    | Arcp => let unopt := double_op FDiv v1 v2 in 
              let opt := double_op_arcp FDiv v1 v2 fm in 
              feq unopt opt (* Here equality is algebraic *)
    | _    => false (* Default *)
    end.
Admitted.
*)

(* contract: Allow floating-point contraction, i.e. FMA *)
Definition double_op_contract {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) (v3 : ll_double) (fm : fast_math)
: M dvalue :=
    match fm, fop with 
    | Contract, FMul => ret (DVALUE_Double (b64_fma FT_Rounding v1 v2 v3))
    | _ ,_            => double_op fop v1 v2
    end.

(*
Lemma contract_equiv {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) (v3 : ll_double) (fm : fast_math): bool :
    match fm with 
    | Contract => let unopt_mul := double_op FMul v1 v2 in 
                  let unopt_add := double_op FAdd unopt_mul v3 in 
                  let opt :=       double_op_contract FMul v1 v2 v3 in 
                  feq unopt_add opt 
    | _       => false (* Default *)
    end.
*)

(* TODO: State optimization theorems in Vellvm logic
    Look at the peephole optimization file

    A peephole optimization is a program transformation subsituting straight code
    for straight code

    Look at the EquivExpr.v file

     Lemma add_commutative : forall b1 b2 τ e1 e2,
      ( OP_IBinop (Add b1 b2) τ e1 e2 )  ≐ [τ] ( OP_IBinop (Add b1 b2) τ e2 e1 ).

    Says that e1 + e2 = e2 + e1


    Lemma add_zero : forall b1 b2 (e:exp dtyp),
    (OP_IBinop (Add b1 b2) (DTYPE_I 32) (EXP_Integer (0)%Z) e) ≐ [DTYPE_I 32] e.

    e + 0 = e

    | OP_IBinop           (iop:ibinop) (t:T) (v1:exp) (v2:exp)

    Definition eq_l2 (t:dtyp) (exp1 : exp dtyp)  (exp2 : exp dtyp) : Prop :=
    forall g l,   (eutt (fun '(g1, (l1, u1)) '(g2, (l2, u2)) => g1 = g2 /\ l1 = l2 /\ uvalue_eq u1 u2) (⟦ exp1 at t ⟧e2 g l) (⟦ exp2 at t ⟧e2 g l)).

  Infix "≐ [ t ]" := (@eq_l2 t) (at level 60).

    Definition interp_cfg2 {R} (t: itree instr_E R) (g: global_env) (l: local_env) : itree (CallE +' IntrinsicE +' MemoryE +' PickE +' OOME +' UBE +' DebugE +' FailureE) (local_env * (global_env * R)) :=
      let L0_trace       := interp_intrinsics t in
      let L1_trace       := interp_global L0_trace g in
      let L2_trace       := interp_local L1_trace l in
      L2_trace.

  (⟦ exp1 at t ⟧e2 g l) is same as saying

  interp_cfg2 (translate exp_to_instr (denote_exp t exp1 )) g l

  (⟦ exp2 at t ⟧e2 g l)) is same as saying

    interp_cfg2 (translate exp_to_instr (denote_exp t exp2 )) g l

g and l are global and local environments respectively

uvalue_eq is a refinement relation for uvalues

 (* Refinement relation for uvalues *)
  (* Definition 5.6 UValue refinement *)
 Variant refine_uvalue: uvalue -> uvalue -> Prop :=
    | UndefPoison: forall dt uv uv1, concretize uv1 (DVALUE_Poison dt) -> uvalue_has_dtyp uv dt -> refine_uvalue uv1 uv
    | RefineConcrete: forall uv1 uv2, (forall (dv:dvalue), concretize uv2 dv -> concretize uv1 dv) -> refine_uvalue uv1 uv2
  .
  #[export] Hint Constructors refine_uvalue : core.

  Definition uvalue_eq (uv1 uv2 : uvalue) : Prop
    := refine_uvalue uv1 uv2 /\ refine_uvalue uv2 uv1

    For concrete values, refinement is reflexive and anything can refine poison
    
    Hence for UndefPoison, it says that if uv1 concretizes to poison and uv has the same type
    as Poison, then uv refines poison

    RefineConcrete says that if uv2 concretizes to dv and uv1 concretizes to dv, then uv2 refines uv1 and vice versa

Therefore the eq_l2 says that if the global and local environments are same 
then the exp1 and exp2 evaluate to the same value
*)
Print eutt.
Definition eq_l2 (t:dtyp) (exp1 : exp dtyp)  (exp2 : exp dtyp) : Prop :=
    forall g l,   (eutt (fun '(g1, (l1, u1)) '(g2, (l2, u2)) => g1 = g2 /\ l1 = l2 /\ uvalue_eq u1 u2) 
    (⟦ exp1 at t ⟧e2 g l) (⟦ exp2 at t ⟧e2 g l)).

Print eq_l2.

(* For floats, the meaning of refinement between dynamic values will no longer be reflexive.
Instead they will carry error bounds 
TODO: Define a bisimulation relation for floats? *)
Variable ε : ll_double.
Print Bcompare.
Definition Blt (x : ll_double) (y : ll_double) : bool :=
    match (Bcompare 53 1024 x y) with 
    | Some Lt => true
    | _       => false
    end.
    
Check Blt.  
Print Babs.
Definition b64_abs (v : ll_double):=
    @Babs 53 1024 (@babs_nan 53 1024) v.

Check exist2.
Check Bcompare.

Check Binary.is_finite.
Search Binary.Babs.
Print Binary.is_finite_strict.
Print B2R.

Definition rounded r:=
(Generic_fmt.round Zaux.radix2 (SpecFloat.fexp 53 1024)
     (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) r).

Definition default_rel : R :=
  / 2 * Raux.bpow Zaux.radix2 (- 53 + 1).

Definition default_abs : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - 1024 - 53).
  
Lemma generic_round_property:
  forall (r: R),
exists delta epsilon : R,
   (delta * epsilon = 0)%R /\
  (Rabs delta <= default_rel)%R /\
  (Rabs epsilon <= default_abs)%R /\
   Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp 53 1024)
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
               r = (r * (1+delta)+epsilon)%R.
Proof.
intros.
destruct (Relative.error_N_FLT Zaux.radix2 (SpecFloat.emin 53 1024) 53 
            prec_gt_0 (fun x0 : Z => negb (Z.even x0)) r)
  as [delta [epsilon [? [? [? ?]]]]].
exists delta, epsilon. unfold default_abs. unfold SpecFloat.emin in H0.
split; [ | split]; auto.
Qed.


Definition b64_minus_bounded (x y : ll_double) :=
    (Rabs (rounded (B2R 53 1024 x - B2R 53 1024 y)) < Raux.bpow Zaux.radix2 1024)%R.

Definition b64_minus_bound (x y : ll_double) :=
    ((Rabs (B2R 53 1024 x) + Rabs (B2R 53 1024 y)) * (1 + default_rel) + default_abs < Raux.bpow Zaux.radix2 1024)%R.    

Lemma b64_minus_bounded_implies_finite (x y : ll_double)
    (Hfinx : is_finite 53 1024 x = true)
    (Hfiny : is_finite 53 1024 y = true):
    b64_minus_bound x y ->
    Binary.is_finite 53 1024 (b64_minus FT_Rounding x y) = true.
Proof.
intros. 
unfold b64_minus_bounded in H. 
pose proof (Bminus_correct 53 1024 prec_gt_0 prec_lt_emax (bminus_nan (emax:=1024)) FT_Rounding x y Hfinx Hfiny).
assert (Raux.Rlt_bool
            (Rabs
            (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp 53 1024)
                (BinarySingleNaN.round_mode FT_Rounding)
                (B2R 53 1024 x - B2R 53 1024 y)))
            (Raux.bpow Zaux.radix2 1024) = true).
{
    apply Raux.Rlt_bool_true. unfold rounded in H.  
    pose proof (@generic_round_property (B2R 53 1024 x - B2R 53 1024 y)%R).
    destruct H1 as [d1 [e1 [Hde1 [Hd1 [He1 Hval1]]]]]. unfold FT_Rounding.
    rewrite Hval1. eapply Rle_lt_trans.
    eapply Rle_trans. eapply Rle_trans.
    eapply Rabs_triang. apply Rplus_le_compat. rewrite Rabs_mult.
    apply Rmult_le_compat_l. apply Rabs_pos. eapply  Rle_trans. apply Rabs_triang.
    rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd1. apply He1.
    apply Rplus_le_compat_r. apply Rmult_le_compat_r. 
    apply Rplus_le_le_0_compat. nra. unfold default_rel. simpl. nra.
    apply Rabs_triang. rewrite Rabs_Ropp. apply H.
} rewrite H1 in H0. apply H0.
Qed. 

Lemma bminus_finite_implies_no_ov (x y : ll_double)
(Hfinx : is_finite 53 1024 x = true)
(Hfiny : is_finite 53 1024 y = true):
is_finite 53 1024 (b64_minus BinarySingleNaN.mode_NE x y) = true ->
(Rabs
   (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp 53 1024)
      (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
      (B2R 53 1024 x - B2R 53 1024 y)) <
 Raux.bpow Zaux.radix2 1024)%R.
Proof.
intros.
pose proof Rle_or_lt (Raux.bpow Zaux.radix2 1024) 
  (Rabs (rounded (B2R 53 1024 x - B2R 53 1024 y)))  as Hor;
  destruct Hor; auto.
apply Raux.Rlt_bool_false in H0. 
unfold b64_minus in H.
pose proof (@Bminus_correct 53 1024 prec_gt_0 prec_lt_emax (bminus_nan (emax:=1024)) BinarySingleNaN.mode_NE x y Hfinx Hfiny).
unfold rounded in H0.  simpl in H0, H1. rewrite H0 in H1.
clear H0. unfold B2FF in H1. destruct H1.
destruct (Bminus 53 1024 prec_gt_0 prec_lt_emax (bminus_nan (emax:=1024)) BinarySingleNaN.mode_NE x y); simpl; try discriminate.
Qed.

(* TODO: Look at the behavior of poison *)
Print uvalue.

Definition double_refine (d1 d2 : uvalue) :=
    match d1, d2 with
    | UVALUE_Poison t1, UVALUE_Poison t2 =>  dtyp_eqb t1 t2
    | UVALUE_Double p1, UVALUE_Double p2 => 
        Binary.is_finite 53 1024 p1 = true /\ is_finite 53 1024 p2 = true /\
        is_finite 53 1024 (b64_minus FT_Rounding p1 p2) = true ->
        exists ε,  (B2R 53 1024 (b64_abs (b64_minus FT_Rounding p1 p2)) <= ε)%R 
    | _, _ => False
    end. 


Check double_refine.
(* Bisimulation relation for floats *)


(* Definition of equivalence *)
(* TODO: Look at the behavior of global and local env *)
Definition eq_fl (t : dtyp) (exp1 : exp dtyp) (exp2 : exp dtyp) :=
    forall g l, (eutt (fun '(g1, (l1, u1)) '(g2, (l2, u2)) => 
                        g1 = g2 /\ l1 = l2 /\ 
                        (* refinement relation for floats *)
                        double_refine u1 u2))
    (⟦ exp1 at t ⟧e2 g l) (⟦ exp2 at t ⟧e2 g l).

Check eq_fl.
Import ListNotations.

Variable a b c : ll_double.
Definition non_fma_blk := {|
  blk_id := (Anon (3)%Z);
  blk_phis := [];
  blk_code := [((IId (Anon (4)%Z)), 
                (INSTR_Op 
                (OP_FBinop FMul [] DTYPE_Double 
                  (EXP_Double a)
                  (EXP_Double b)
                  (*(EXP_Ident (ID_Local (Anon (0)%Z))) 
                  (EXP_Ident (ID_Local (Anon (1)%Z))) *)
                ))); 
                ((IId (Anon (5)%Z)), 
                (INSTR_Op (OP_FBinop FAdd [] DTYPE_Double 
                  (EXP_Ident (ID_Local (Anon (4)%Z)))
                  (EXP_Double c) 
                  (*(EXP_Ident (ID_Local (Anon (2)%Z))) *)
                )))
              ];
  blk_term := (TERM_Ret (DTYPE_Double, 
                        (EXP_Ident (ID_Local (Anon (5)%Z)))));
  blk_comments := None
  
|}.

Definition denote_nonfma_blk := denote_block non_fma_blk (Anon (3)%Z) None.


Definition fma_blk := {|
  blk_id := (Anon (3)%Z);
  blk_phis := [];
  blk_code := [((IId (Anon (4)%Z)),
                (INSTR_Call 
                (DTYPE_Double, (EXP_Ident (ID_Global (Name "llvm.fmuladd.f64")))) 
                [((DTYPE_Double, EXP_Double a), []);
                 ((DTYPE_Double, EXP_Double b), []);
                 ((DTYPE_Double, EXP_Double c), [])]
                (*[((TYPE_Double, (EXP_Ident (ID_Local (Anon (0)%Z)))), []); 
                 ((TYPE_Double, (EXP_Ident (ID_Local (Anon (1)%Z)))), []); 
                 ((TYPE_Double, (EXP_Ident (ID_Local (Anon (2)%Z)))), [])] *)
                [ANN_tail Tail]))
              ];
  blk_term := (TERM_Ret (DTYPE_Double, 
                        (EXP_Ident (ID_Local (Anon (4)%Z)))));
  blk_comments := None
  
|}.

Definition denote_fma_blk := denote_block fma_blk (Anon (3)%Z) None.

Print interp_cfg2.


Print defined_intrinsics.
Print  handle_intrinsics.

(*
Property 1: "The local 5 in l1 refines the local 4 in l2"

forall k1 k2, k1 = 4 ∧ k2 = 5 ∧ v(k1) = l1 ∧ v(k2) = l2 -> double_refine l1 l2

Property 2: "The two memories are equal other than locals 4 and 5"

(forall k, k <> 4 /\ k <> 5 -> l1 k = l2 k)

(key_equal 5 4 l1 l2) /\ (something about key 4 in l1) /\ (forall k, k <> 4 /\ k <> 5 -> l1 k = l2 k) 


https://github.com/vellvm/vellvm/blob/dev/src/rocq/Theory/LocalEquiv.v
*)


Lemma finite_sum_prod_implies_finite_prod (x y z : ll_double):
is_finite 53 1024
(Bits.b64_plus BinarySingleNaN.mode_NE (Bits.b64_mult BinarySingleNaN.mode_NE x y) z) = true ->
is_finite 53 1024 (Bits.b64_mult BinarySingleNaN.mode_NE x y) = true.
Proof.
intros. 
pose (Bits.b64_mult BinarySingleNaN.mode_NE x y) as l. 
fold l in H. fold l.
destruct l; simpl; auto.
destruct s; simpl in *;(unfold Bits.b64_plus, Bplus in H; simpl in H; destruct z; simpl in *;
auto;
destruct s; simpl in *; auto; auto; auto; auto).
Qed.

Lemma finite_sum_prod_implies (x y z : ll_double):
is_finite 53 1024
(Bits.b64_plus BinarySingleNaN.mode_NE (Bits.b64_mult BinarySingleNaN.mode_NE x y) z) = true ->
is_finite 53 1024 x = true /\
is_finite 53 1024 y = true /\
is_finite 53 1024 z = true.
Proof.
intros. 
assert (is_finite 53 1024 (Bits.b64_mult BinarySingleNaN.mode_NE x y) = true /\ is_finite 53 1024 z = true).
{ 
    split. apply finite_sum_prod_implies_finite_prod with z. apply H. 

    pose (Bits.b64_mult BinarySingleNaN.mode_NE x y) as l. 
    fold l in H. fold l. 
    destruct z; simpl; auto.
    destruct s; simpl in *. unfold Bits.b64_plus, Bplus,BinarySingleNaN.Bplus in H; simpl in H. 
    destruct l; simpl in *. auto. destruct s; simpl in *. auto. auto. auto. auto. 
    destruct l; simpl in *. auto. unfold Bits.b64_plus, Bplus,BinarySingleNaN.Bplus in H; simpl in H. 
    destruct s; simpl in *. auto. auto. auto. auto. 
    unfold Bits.b64_plus, Bplus,BinarySingleNaN.Bplus in H; simpl in H. 
    destruct l; simpl in *. auto. destruct s; simpl in *. auto. auto. auto. auto.  
} destruct H0.
repeat split;try apply H1.
+ unfold Bits.b64_mult, Bmult,BinarySingleNaN.Bmult in H0. destruct x; simpl in *; auto. 
  destruct y; simpl in *; auto.
+ unfold Bits.b64_mult, Bmult,BinarySingleNaN.Bmult in H0. destruct y; simpl in *; auto. 
destruct x; simpl in *; auto. destruct x; simpl in *; auto. 
Qed.

Lemma bfma_finite_implies_no_ov (x y z : ll_double)
(Hfinx : is_finite 53 1024 x = true)
(Hfiny : is_finite 53 1024 y = true)
(Hfinz : is_finite 53 1024 z = true):
is_finite 53 1024 (Intrinsics.b64_fma BinarySingleNaN.mode_NE x y z) = true ->
(Rabs
   (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp 53 1024)
      (BinarySingleNaN.round_mode FT_Rounding)
      (B2R 53 1024 x * B2R 53 1024 y + B2R 53 1024 z)) <
 Raux.bpow Zaux.radix2 1024)%R.
Proof.
intros.
pose proof Rle_or_lt (Raux.bpow Zaux.radix2 1024) 
  (Rabs (rounded (B2R 53 1024 x * B2R 53 1024 y + B2R 53 1024 z)))  as Hor;
  destruct Hor; auto.
apply Raux.Rlt_bool_false in H0. 
unfold Intrinsics.b64_fma in H.
pose proof (@Bfma_correct 53 1024 eq_refl eq_refl Floats.Float.fma_nan BinarySingleNaN.mode_NE x y z Hfinx Hfiny Hfinz).
unfold rounded in H0. simpl in H0, H1. rewrite H0 in H1.
clear H0. unfold B2FF in H1. simpl in H.  
destruct
((Bfma (Zpos (xI (xO (xI (xO (xI xH))))))
(Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))
(@eq_refl comparison Lt)
(@eq_refl comparison
   (PosDef.Pos.compare (xI (xO (xI (xO (xI xH)))))
      (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))))))
Floats.Float.fma_nan BinarySingleNaN.mode_NE x y z)); try discriminate.
Qed.

Lemma bplus_finite_implies_no_ov (x y z : ll_double)
(Hfinmab : is_finite 53 1024 (Bits.b64_mult BinarySingleNaN.mode_NE x y) = true)
(Hfinz : is_finite 53 1024 z = true):
is_finite 53 1024 (Bits.b64_plus BinarySingleNaN.mode_NE (Bits.b64_mult BinarySingleNaN.mode_NE x y) z) = true ->
(Rabs
   (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp 53 1024)
      (BinarySingleNaN.round_mode FT_Rounding)
      (B2R 53 1024 (Bits.b64_mult BinarySingleNaN.mode_NE x y) + B2R 53 1024 z)) <
 Raux.bpow Zaux.radix2 1024)%R.
Proof.
intros.
pose proof Rle_or_lt (Raux.bpow Zaux.radix2 1024) 
  (Rabs (rounded (B2R 53 1024 (Bits.b64_mult BinarySingleNaN.mode_NE x y) + B2R 53 1024 z)))  as Hor;
  destruct Hor; auto.
apply Raux.Rlt_bool_false in H0. 
unfold Bits.b64_plus in H.
pose proof (@Bplus_correct 53 1024 Bits.Hprec_subproof1 Bits.Hprec_emax_subproof0 Bits.binop_nan_pl64 BinarySingleNaN.mode_NE (Bits.b64_mult BinarySingleNaN.mode_NE x y) z Hfinmab Hfinz).
unfold rounded in H0.  simpl in H0, H1. rewrite H0 in H1.
clear H0. unfold B2FF in H1. destruct H1.    
destruct (Bplus 53 1024 Bits.Hprec_subproof1 Bits.Hprec_emax_subproof0
Bits.binop_nan_pl64 BinarySingleNaN.mode_NE
(Bits.b64_mult BinarySingleNaN.mode_NE x y) z); simpl; try discriminate.
Qed.

Lemma bmult_finite_implies_no_ov (x y : ll_double):
is_finite 53 1024 (Bits.b64_mult BinarySingleNaN.mode_NE x y) = true ->
(Rabs
   (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp 53 1024)
      (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
      (B2R 53 1024 x * B2R 53 1024 y)) <
 Raux.bpow Zaux.radix2 1024)%R.
Proof.
intros.
pose proof Rle_or_lt (Raux.bpow Zaux.radix2 1024) 
  (Rabs (rounded (B2R 53 1024 x * B2R 53 1024 y)))  as Hor;
  destruct Hor; auto.
apply Raux.Rlt_bool_false in H0. 
unfold Bits.b64_mult in H.
pose proof (@Bmult_correct 53 1024 Bits.Hprec_subproof1 Bits.Hprec_emax_subproof0 Bits.binop_nan_pl64 BinarySingleNaN.mode_NE x y).
unfold rounded in H0.  simpl in H0, H1. rewrite H0 in H1.
clear H0. unfold B2FF in H1. 
destruct (Bmult 53 1024 Bits.Hprec_subproof1 Bits.Hprec_emax_subproof0
Bits.binop_nan_pl64 BinarySingleNaN.mode_NE x y); simpl; try discriminate.
Qed.

Lemma refinement_rel_bfma_non_fma:
double_refine (UVALUE_Double (Intrinsics.b64_fma FT_Rounding a b c))
  (UVALUE_Double
     (Bits.b64_plus FT_Rounding (Bits.b64_mult FT_Rounding a b) c)).
Proof.
unfold double_refine. intros [Hfa [Hfb Hfmab]]. 
exists ((Rabs (B2R 53 1024 a * B2R 53 1024 b + B2R 53 1024 c) * default_rel + default_abs +
Rabs (B2R 53 1024 a * B2R 53 1024 b) * (2 * default_rel + default_rel²) +
default_abs * (1 + default_rel) + Rabs (B2R 53 1024 c) * default_rel + default_abs) *
(1 + default_rel) + default_abs)%R.
unfold b64_abs.
rewrite B2R_Babs. unfold b64_minus.
pose proof (Bminus_correct 53 1024 prec_gt_0 prec_lt_emax (bminus_nan
(emax:=1024)) FT_Rounding (Intrinsics.b64_fma FT_Rounding a b c)
(Bits.b64_plus FT_Rounding (Bits.b64_mult FT_Rounding a b) c)).
specialize (H Hfa Hfb).
assert (Raux.Rlt_bool
            (Rabs
            (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp 53 1024)
                (BinarySingleNaN.round_mode FT_Rounding)
                (B2R 53 1024 (Intrinsics.b64_fma FT_Rounding a b c) -
                B2R 53 1024
                    (Bits.b64_plus FT_Rounding (Bits.b64_mult FT_Rounding a b) c))))
            (Raux.bpow Zaux.radix2 1024)).
{
    apply Raux.Rlt_bool_true.
    apply bminus_finite_implies_no_ov; auto.
} rewrite H0 in H. destruct H as [Hval [Hfinite Hsign]].
rewrite Hval.
pose proof (@generic_round_property
(B2R 53 1024 (Intrinsics.b64_fma FT_Rounding a b c) -
           B2R 53 1024
             (Bits.b64_plus FT_Rounding (Bits.b64_mult FT_Rounding a b) c))%R).
destruct H as [d1 [e1 [Hde1 [Hd1 [He1 Hval1]]]]]. unfold FT_Rounding in *.
rewrite Hval1.
pose proof (Bfma_correct 53 1024 eq_refl eq_refl Floats.Float.fma_nan FT_Rounding a b c).
unfold Intrinsics.b64_fma.
assert (is_finite 53 1024 a = true) as Hfina. { pose proof (finite_sum_prod_implies a b c). apply H1. auto. }
assert (is_finite 53 1024 b = true) as Hfinb by (pose proof (finite_sum_prod_implies a b c); apply H1; auto).
assert (is_finite 53 1024 c = true) as Hfinc by (pose proof (finite_sum_prod_implies a b c); apply H1; auto).
specialize (H Hfina Hfinb Hfinc).
assert (Raux.Rlt_bool
(Rabs
   (Generic_fmt.round
      Zaux.radix2
      (SpecFloat.fexp 53 1024)
      (BinarySingleNaN.round_mode
         FT_Rounding)
         (B2R 53 1024 a * B2R 53 1024 b +
         B2R 53 1024 c)%R))
(Raux.bpow Zaux.radix2 1024) = true).
{
    apply Raux.Rlt_bool_true. apply bfma_finite_implies_no_ov; auto.
} unfold FT_Rounding in H. simpl in H, H1. rewrite H1 in H.
destruct H as [Hval2 _  ]. simpl.
rewrite Hval2.
pose proof (@generic_round_property (B2R 53 1024 a * B2R 53 1024 b +
B2R 53 1024 c)%R).
destruct H as [d2 [e2 [Hde2 [Hd2 [He2 Hval3]]]]].
simpl in Hval3. rewrite Hval3.
unfold Bits.b64_plus. 
pose proof (Bplus_correct 53 1024 Bits.Hprec_subproof1 Bits.Hprec_emax_subproof0 Bits.binop_nan_pl64 BinarySingleNaN.mode_NE
(Bits.b64_mult BinarySingleNaN.mode_NE a b) c).
assert (is_finite 53 1024
            (Bits.b64_mult BinarySingleNaN.mode_NE a b) = true).
{ apply finite_sum_prod_implies_finite_prod with c. auto. }
assert (is_finite 53 1024 c = true) by (pose proof (finite_sum_prod_implies a b c) as Hf; apply Hf; auto).
specialize (H H2 H3).
assert (Raux.Rlt_bool
(Rabs
   (Generic_fmt.round Zaux.radix2
      (SpecFloat.fexp 53 1024)
      (BinarySingleNaN.round_mode
         BinarySingleNaN.mode_NE)
      (B2R 53 1024
         (Bits.b64_mult
            BinarySingleNaN.mode_NE a b) +
       B2R 53 1024 c)))
(Raux.bpow Zaux.radix2 1024) = true).
{
    apply Raux.Rlt_bool_true. apply bplus_finite_implies_no_ov; auto.
}
rewrite H4 in H.
destruct H as [Hval4 _].
rewrite Hval4.
pose proof (@generic_round_property (B2R 53 1024
(Bits.b64_mult
   BinarySingleNaN.mode_NE a b) +
B2R 53 1024 c)%R).
destruct H as [d3 [e3 [Hde3 [Hd3 [He3 Hval5]]]]]. 
rewrite Hval5. unfold Bits.b64_mult.
pose proof (Bmult_correct 53 1024 Bits.Hprec_subproof1 Bits.Hprec_emax_subproof0 Bits.binop_nan_pl64 BinarySingleNaN.mode_NE a b).
assert (Raux.Rlt_bool
(Rabs
   (Generic_fmt.round Zaux.radix2
      (SpecFloat.fexp 53 1024)
      (BinarySingleNaN.round_mode
         BinarySingleNaN.mode_NE)
      (B2R 53 1024 a * B2R 53 1024 b)))
(Raux.bpow Zaux.radix2 1024) = true).
{
    apply Raux.Rlt_bool_true. apply bmult_finite_implies_no_ov;auto.
}
rewrite H5 in H. destruct H as [Hval6 _].
rewrite Hval6.
pose proof (@generic_round_property (B2R 53 1024 a * B2R 53 1024 b)%R).
destruct H as [d4 [e4 [Hde4 [Hd4 [He4 Hval7]]]]]. 
rewrite Hval7.
assert (((B2R 53 1024 a * B2R 53 1024 b +
B2R 53 1024 c) *
(1 + d2) + e2 -
((B2R 53 1024 a * B2R 53 1024 b *
 (1 + d4) + e4 + B2R 53 1024 c) *
(1 + d3) + e3))%R = 
((B2R 53 1024 a * B2R 53 1024 b + B2R 53 1024 c) * d2 + e2 - 
(B2R 53 1024 a * B2R 53 1024 b) * (d4 + d3 + d3 * d4) - 
e4 * (1 + d3) - (B2R 53 1024 c) * d3 - e3)%R
) by nra. rewrite H.
eapply Rle_trans. eapply Rle_trans.
apply Rabs_triang. eapply Rle_trans.
apply Rplus_le_compat. rewrite Rabs_mult.
apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang. rewrite Rabs_Ropp.
apply Rplus_le_compat. eapply Rle_trans.
apply Rabs_triang. rewrite Rabs_Ropp.
apply Rplus_le_compat. eapply Rle_trans.
apply Rabs_triang. rewrite Rabs_Ropp. 
apply Rplus_le_compat. eapply Rle_trans.
apply Rabs_triang. rewrite Rabs_Ropp.
apply Rplus_le_compat.
eapply Rle_trans. apply Rabs_triang.
apply Rplus_le_compat. rewrite Rabs_mult. 
apply Rmult_le_compat_l. apply Rabs_pos.
apply Hd2. apply He2. rewrite Rabs_mult.
apply Rmult_le_compat_l. apply Rabs_pos.
eapply Rle_trans. apply Rabs_triang.
apply Rplus_le_compat. eapply Rle_trans.
apply Rabs_triang. apply Rplus_le_compat.
apply Hd4. apply Hd3. rewrite Rabs_mult.
apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
apply Hd3. apply Hd4. rewrite Rabs_mult.
apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos.
apply He4. eapply Rle_trans. apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd3.
rewrite Rabs_mult. apply Rmult_le_compat_l. apply Rabs_pos.
apply Hd3. apply He3. eapply Rle_trans. apply Rabs_triang.
rewrite Rabs_R1. apply Rplus_le_compat_l. apply Hd1. apply He1.
apply Rle_refl.
replace (default_rel + default_rel)%R with (2 * default_rel)%R by nra.
replace (default_rel * default_rel)%R with (Rsqr default_rel)%R by (unfold Rsqr;nra).
apply Rle_refl.
Qed.

Lemma fma_optim_correct:
forall g l,
  eutt (fun '(g1, (l1, u1)) '(g2, (l2, u2)) => 
  g1 = g2 /\ l1 = l2 /\ 
  (* refinement relation for floats *)
  match u1, u2 with
  | inr u1_v, inr u2_v => 
        double_refine u1_v u2_v
  | _, _ => False
  end )
  (interp_cfg2 denote_fma_blk g l) (interp_cfg2 denote_nonfma_blk g l).
Proof.
intros.
unfold interp_cfg2. unfold interp_cfg1. unfold denote_fma_blk, denote_nonfma_blk.
cbn. rewrite interp_intrinsics_bind. rewrite interp_global_bind.
rewrite interp_local_bind. rewrite interp_intrinsics_bind.
rewrite interp_global_bind.
rewrite interp_local_bind.
rewrite interp_intrinsics_ret.
rewrite interp_global_ret.
rewrite interp_local_ret. simpl.  
simpl. unfold interp_intrinsics. unfold interp_intrinsics_h.
unfold handle_intrinsics. simpl.
unfold interp.
tau_steps.
unfold observe.
simpl.
cbn.
destruct (@RelDec.rel_dec_p int_ast
(@eq int_ast) eq_dec_int
Z.RelDec_Correct_zeq 4%Z 4%Z); try Lia.lia.
simpl.
tau_steps.
unfold observe.
simpl.
cbn.
destruct (@RelDec.rel_dec_p int_ast
(@eq int_ast) eq_dec_int
Z.RelDec_Correct_zeq 5%Z 5%Z); try Lia.lia.
simpl.
tau_steps.
unfold observe.
simpl.
cbn.
apply eutt_Ret.
repeat split.
unfold FMapAList.alist_add. 

Print local_env.
Print FMapAList.alist.


f_equal. admit.
admit.
apply refinement_rel_bfma_non_fma.

Admitted. 
(* TODO: move fma intrinsic definition to vellvm and retry proof *)
End FastMath. 

Section F_intrinsics.
Import LLVMIO.    

Import ListNotations.
(* TODO: Add intrinsics for FMA in Vellvm *)
(* Registering the fmul_add intrinsics *)
Definition fmul_add_64 : declaration typ :=
    {|
        dc_name := Name "llvm.fmuladd.f64";
        dc_type := TYPE_Function TYPE_Double [TYPE_Double; TYPE_Double; TYPE_Double] false;
        dc_param_attrs := ([], [[]]);
        dc_attrs       := [];
        dc_annotations  := []
    |}.

(* Extending the defined intrinsics in Vellvm VIR *)
Definition defined_intrinsics_decls' :=
    defined_intrinsics_decls ++ [fmul_add_64].

(* Intrinsics semantic functions *)

(* Internally, invocation of an intrinsic looks no different than that of 
an external function call, so each LLVM instrinsic instruction should produce
a Call effect 

Each intrinsic is identified by its name (a string) and its denotation 
is given by a function from a list of dynamic values to a dynamic value
(for possibly an error).

This layer is useful for implementing "Pure value" intrtinsics like 
floating-point operations, etc. Also note that such intrinsics cannot 
themselves generate any other effects.

Eacg (pure) instrinsic is defined by a function of the following type.

- each intrinsic should "morally" be a total function: assuming the LLVM
program is well formed, the instrinsic should always produce an LLVM value
(whuch itself might be a posion or undef)

- error should be returned only in the case that the LLVM program is ill-formed
(e.g., if the wrong number and/or type of arguments is given to the intrinsic)

The semantic_function is a total function, which takes in a list of 
dvalues and returns a dvalue if the LLVM program is well-defined or 
returns an error if it is ill-defined

intrinsic_definitions is an association list which maps 
intrinsic names to their semantic definition.

The intrinsics interpreter looks for Calls to instrinsics defined 
by its argument and runs their semantic function, raising 
an error in case of exception.

Unknown Calls (either to other intrinsics or external calls)
are passed though unchanged


(* Call to an intrinsic whose implementation do not rely on the implementation of the memory model *)
(* Intrinsics may raise an exception by returning inl *)
Variant IntrinsicE : Type -> Type :=
    | Intrinsic : forall (t:dtyp) (f:string) (args:list dvalue), IntrinsicE (uvalue + dvalue).
    
The reason I need to include LLVMInteractions is that
intrinsics are defined using the intrinsicE effect    
    
*)

(* TODO: Revisit this because ret (inr uvalue)*)
Definition llvm_fmuladd_f64 : semantic_function :=
    fun args =>
        match args with 
        | [DVALUE_Double a; DVALUE_Double b; DVALUE_Double c] =>
                let fma_op := b64_fma FT_Rounding a b c in
                ret (DVALUE_Double fma_op)
        | _ => failwith "llvm_fmuladd_f64 got incorrect / ill-typed inputs"
        end.

Locate semantic_function.
Definition defined_intrinsics' :=
    defined_intrinsics ++ [(fmul_add_64, llvm_fmuladd_f64)].

End F_intrinsics.




