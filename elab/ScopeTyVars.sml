(*
 * (c) Andreas Rossberg 1999-2013
 *
 * Standard ML scope of type variables
 *
 * Definition, Section 4.6
 *)

structure ScopeTyVars : SCOPE_TYVARS =
struct
  (* Import *)

  open SyntaxCore
  open Annotation
  structure D = DerivedFormsCore

  type TyVarSet = TyVarSet.set


  (* Helpers *)

  val op+ = TyVarSet.union

  fun ?tyvarsX NONE    = TyVarSet.empty
    | ?tyvarsX(SOME x) = tyvarsX x


  (* Operation *)

  fun unguardedTyVarsAtExp(SCONAtExp(_)@@_) =
        TyVarSet.empty
    | unguardedTyVarsAtExp(UNITAtExpX @@ _) =
        TyVarSet.empty
    | unguardedTyVarsAtExp(IDAtExp(_, _)@@_) =
        TyVarSet.empty
    | unguardedTyVarsAtExp(RECORDAtExp(exprow_opt)@@_) =
        ?unguardedTyVarsExpRow exprow_opt
    | unguardedTyVarsAtExp(LETAtExp(dec, exp)@@_) =
        unguardedTyVarsDec dec + unguardedTyVarsExp exp
    | unguardedTyVarsAtExp(PARAtExp(exp)@@_) =
        unguardedTyVarsExp exp
    | unguardedTyVarsAtExp(TUPLEAtExpX(exps)@@_) = 
        List.foldl (op+) (TyVarSet.empty) (List.map unguardedTyVarsExp exps)
    | unguardedTyVarsAtExp(LISTAtExpX(exps)@@_) = 
        List.foldl (op+) (TyVarSet.empty) (List.map unguardedTyVarsExp exps)

  and unguardedTyVarsExpRow(ExpRow(lab, exp, exprow_opt)@@_) =
        unguardedTyVarsExp exp + ?unguardedTyVarsExpRow exprow_opt

  and unguardedTyVarsExp(ATExp(atexp)@@_) =
        unguardedTyVarsAtExp atexp
    | unguardedTyVarsExp(APPExp(exp, atexp)@@_) =
        unguardedTyVarsExp exp + unguardedTyVarsAtExp atexp
    | unguardedTyVarsExp(COLONExp(exp, ty)@@_) =
        unguardedTyVarsExp exp + unguardedTyVarsTy ty
    | unguardedTyVarsExp(HANDLEExp(exp, match)@@_) =
        unguardedTyVarsExp exp + unguardedTyVarsMatch match
    | unguardedTyVarsExp(RAISEExp(exp)@@_) =
        unguardedTyVarsExp exp
    | unguardedTyVarsExp(FNExp(match)@@_) =
        unguardedTyVarsMatch match
    | unguardedTyVarsExp(CASEExpX(exp1, match)@@A) = 
      unguardedTyVarsExp(D.CASEExp'(exp1, match)@@A)
    | unguardedTyVarsExp(IFExpX(exp1, exp2, exp3)@@A) = 
      unguardedTyVarsExp(D.IFExp'(exp1, exp2, exp3)@@A)
    | unguardedTyVarsExp(ORELSEExpX(exp1, exp2)@@A) = 
      unguardedTyVarsExp(D.ORELSEExp'(exp1, exp2)@@A)
    | unguardedTyVarsExp(ANDALSOExpX(exp1, exp2)@@A) = 
      unguardedTyVarsExp(D.ANDALSOExp'(exp1, exp2)@@A)
    | unguardedTyVarsExp(INFIXExpX(exp, atexp)@@A) = 
      unguardedTyVarsExp(APPExp(exp, atexp)@@A)


  and unguardedTyVarsMatch(Match(mrule, match_opt)@@_) =
        unguardedTyVarsMrule mrule + ?unguardedTyVarsMatch match_opt

  and unguardedTyVarsMrule(Mrule(pat, exp)@@_) =
        unguardedTyVarsPat pat + unguardedTyVarsExp exp
    | unguardedTyVarsMrule (FmruleX(pat, ty_opt, exp)@@_) = 
      unguardedTyVarsPat pat + ?unguardedTyVarsTy ty_opt +
      unguardedTyVarsExp exp

  and unguardedTyVarsDec(VALDec(_, _)@@_) =
        TyVarSet.empty
    | unguardedTyVarsDec(TYPEDec(_)@@_) =
        TyVarSet.empty
    | unguardedTyVarsDec(DATATYPEDec(_)@@_) =
        TyVarSet.empty
    | unguardedTyVarsDec(DATATYPE2Dec(_, _)@@_) =
        TyVarSet.empty
    | unguardedTyVarsDec(ABSTYPEDec(datbind, dec)@@_) =
        unguardedTyVarsDec dec
    | unguardedTyVarsDec(EXCEPTIONDec(exbind)@@_) =
        unguardedTyVarsExBind exbind
    | unguardedTyVarsDec(LOCALDec(dec1, dec2)@@_) =
        unguardedTyVarsDec dec1 + unguardedTyVarsDec dec2
    | unguardedTyVarsDec(OPENDec(_)@@_) =
        TyVarSet.empty
    | unguardedTyVarsDec(EMPTYDec@@_) =
        TyVarSet.empty
    | unguardedTyVarsDec(SEQDec(dec1, dec2)@@_) =
        unguardedTyVarsDec dec1 + unguardedTyVarsDec dec2

  and unguardedTyVarsValBind(PLAINValBind(pat, exp, valbind_opt)@@_) =
        unguardedTyVarsPat pat + unguardedTyVarsExp exp +
          ?unguardedTyVarsValBind valbind_opt
    | unguardedTyVarsValBind(RECValBind(valbind)@@_) =
        unguardedTyVarsValBind valbind
    | unguardedTyVarsValBind (FValBindX(vid, match, _, valbind_opt)@@_) = 
      unguardedTyVarsMatch match + ?unguardedTyVarsValBind valbind_opt

  and unguardedTyVarsExBind(NEWExBind(_, vid, ty_opt, exbind_opt)@@_) =
        ?unguardedTyVarsTy ty_opt + ?unguardedTyVarsExBind exbind_opt
    | unguardedTyVarsExBind(EQUALExBind(_, vid, _, longvid, exbind_opt)@@_) =
        ?unguardedTyVarsExBind exbind_opt

  and unguardedTyVarsAtPat(WILDCARDAtPat@@_) =
        TyVarSet.empty
    | unguardedTyVarsAtPat(SCONAtPat(_)@@_) =
        TyVarSet.empty
    | unguardedTyVarsAtPat(IDAtPat(_, _)@@_) =
        TyVarSet.empty
    | unguardedTyVarsAtPat(UNITAtPatX@@_) =
        TyVarSet.empty
    | unguardedTyVarsAtPat(RECORDAtPat(patrow_opt)@@_) =
        ?unguardedTyVarsPatRow patrow_opt
    | unguardedTyVarsAtPat(PARAtPat(pat)@@_) =
        unguardedTyVarsPat pat
    | unguardedTyVarsAtPat(TUPLEAtPatX(pats)@@_) =
        List.foldl (op+) (TyVarSet.empty) (List.map unguardedTyVarsPat pats)   
    | unguardedTyVarsAtPat(LISTAtPatX(pats)@@_) =
        List.foldl (op+) (TyVarSet.empty) (List.map unguardedTyVarsPat pats)             

  and unguardedTyVarsPatRow(DOTSPatRow@@_) =
        TyVarSet.empty
    | unguardedTyVarsPatRow(FIELDPatRow(lab, pat, patrow_opt)@@_) =
        unguardedTyVarsPat pat + ?unguardedTyVarsPatRow patrow_opt

  and unguardedTyVarsPat(ATPat(atpat)@@_) =
        unguardedTyVarsAtPat atpat
    | unguardedTyVarsPat(CONPat(_, longvid, atpat)@@_) =
      unguardedTyVarsAtPat atpat
    | unguardedTyVarsPat(INFIXPatX(_, longvid, atpat)@@_) =
        unguardedTyVarsAtPat atpat
    | unguardedTyVarsPat(COLONPat(pat, ty)@@_) =
        unguardedTyVarsPat pat + unguardedTyVarsTy ty
    | unguardedTyVarsPat(ASPat(_, vid, ty_opt, pat)@@_) =
        ?unguardedTyVarsTy ty_opt + unguardedTyVarsPat pat

  and unguardedTyVarsTy(VARTy(tyvar@@_)@@_) =
        TyVarSet.singleton tyvar
    | unguardedTyVarsTy(RECORDTy(tyrow_opt)@@_) =
        ?unguardedTyVarsTyRow tyrow_opt
    | unguardedTyVarsTy(CONTy(tyseq, longtycon)@@_) =
        unguardedTyVarsTyseq tyseq
    | unguardedTyVarsTy(ARROWTy(ty, ty')@@_) =
        unguardedTyVarsTy ty + unguardedTyVarsTy ty'
    | unguardedTyVarsTy(PARTy(ty)@@_) =
        unguardedTyVarsTy ty
    | unguardedTyVarsTy(TUPLETyX(ty)@@A) =
        unguardedTyVarsTy(D.TUPLETy'(ty)@@A)


  and unguardedTyVarsTyRow(TyRow(lab, ty, tyrow_opt)@@_) =
        unguardedTyVarsTy ty + ?unguardedTyVarsTyRow tyrow_opt

  and unguardedTyVarsTyseq(Seq(tys)@@_) =
        List.foldl (fn(ty, U) => unguardedTyVarsTy ty + U) TyVarSet.empty tys


  (* Export *)

  val unguardedTyVars = unguardedTyVarsValBind
end;
