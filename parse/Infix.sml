(*
 * (c) Andreas Rossberg 1999-2013
 *
 * Standard ML infix resolution
 *
 * Definition, Section 2.6
 *)


structure Infix :> INFIX =
struct
  (* Import *)

  open SyntaxCore
  open AnnotationCore
  open Error


  (* Types *)

  datatype Assoc = LEFT | RIGHT

  type InfStatus = Assoc * int
  type InfEnv    = InfStatus VIdMap.map         (* [J] *)


  (* Modifying infix environments *)

  val empty = VIdMap.empty

  fun assign(J, vids, infstatus) =
        List.foldl (fn(vid, J) => VIdMap.insert(J, vid, infstatus)) J vids

  fun cancel(J, vids) =
        List.foldl (fn(vid, J) => VIdMap.delete(J, vid)) J vids


  (* Categorisation of atomic expressions and patterns *)

  datatype 'a FixityCategory =
      NONFIX of 'a
    | INFIX  of 'a * VId * InfStatus

  fun isInfix J (longvid) =
        LongVId.isShort longvid andalso
        VIdMap.find(J, LongVId.toId longvid) <> NONE

  fun categoriseLongVId J (atomic, longvid@@A) =
        if LongVId.isShort longvid then
          let
            val vid = LongVId.toId longvid
          in
            case VIdMap.find(J, vid) of
              NONE           => NONFIX(atomic)
            | SOME infstatus => INFIX(atomic, vid@@A, infstatus)
          end
        else
          NONFIX(atomic)

  fun categoriseAtExp J (atexp as IDAtExp(NONE, longvid)@@_) =
        categoriseLongVId J (atexp, longvid)
    | categoriseAtExp J atexp =
        NONFIX(atexp)

  fun categoriseAtPat J (atpat as IDAtPat(NONE, longvid)@@_) =
        categoriseLongVId J (atpat, longvid)
    | categoriseAtPat J atpat =
        NONFIX(atpat)


  (* Resolving infixing [Section 2.6] *)

  fun parse(app, infapp, es) =
      let
        fun loop(NONFIX(e)::[], []) = e
          | loop(NONFIX(e2)::NONFIX(e1)::s', i) =
              (* reduce nonfix application *)
              loop(NONFIX(app(e1, e2))::s', i)
          | loop(s, NONFIX(e)::i') =
              (* shift *)
              loop(NONFIX(e)::s, i')
          | loop(s as NONFIX(e)::[], INFIX(x)::i') =
              (* shift *)
              loop(INFIX(x)::s, i')
          | loop(NONFIX(e2)::INFIX(e, _, _)::NONFIX(e1)::s', []) =
              (* reduce infix application *)
              loop(NONFIX(infapp(e1, e, e2))::s', [])
          | loop(
              s as NONFIX(e2)::INFIX(e, _, (a1, p1))::NONFIX(e1)::s',
              i as INFIX(x2 as (_@@A, _, (a2, p2)))::i'
            ) =
              if p1 > p2 then
                (* reduce infix application *)
                loop(NONFIX(infapp(e1, e, e2))::s', i)
              else if p1 < p2 then
                (* shift *)
                loop(INFIX(x2)::s, i')
              else if a1 <> a2 then
                error(Source.over(loc(annotation e), loc A),
                  "conflicting infix associativity")
              else if a1 = LEFT then
                (* reduce infix application *)
                loop(NONFIX(infapp(e1, e, e2))::s', i)
              else (* a1 = RIGHT *)
                (* shift *)
                loop(INFIX(x2)::s, i')
          | loop(INFIX(_, vid@@A, _)::s, []) =
              errorVId(loc A, "misplaced infix identifier ", vid)
          | loop(INFIX(x)::s, INFIX(_, vid@@A, _)::i) =
              errorVId(loc A, "misplaced infix identifier ", vid)
          | loop([], INFIX(_, vid@@A, _)::i) =
              errorVId(loc A, "misplaced infix identifier ", vid)
          | loop _ =
              raise Fail "Infix.parse: inconsistency"
      in
        loop([], es)
      end


  (* Resolving infixed expressions [Section 2.6] *)

  fun atExp(atexp) = ATExp(atexp)@@at(atexp)

  fun appExp(atexp1, atexp2) =
      let
        val appExp = APPExp(atExp(atexp1), atexp2)@@over(atexp1, atexp2)
      in
        PARAtExp(appExp)@@at(appExp)
      end

  fun appExp'(atexp1, atexp2) =
      let
          val appExp = INFIXExpX(atExp(atexp1), atexp2)@@over(atexp1, atexp2)
      in
          PARAtExp(appExp)@@at(appExp)
      end

  fun pairExp(atexp1, atexp2) =
      let
          val expList = [atExp atexp1, atExp atexp2]
      in
          (TUPLEAtExpX expList)@@over(atexp1, atexp2)
        (* RECORDAtExp(SOME exprow1)@@at(exprow1) *)
      end

  fun infExp(atexp1, IDAtExp(NONE, longvid)@@A, atexp2) =
        appExp'(IDAtExp(NONE, longvid)@@A, pairExp(atexp1, atexp2))
    | infExp(_, _, _) =
        raise Fail "Infix.infExp: inconsistency"

  fun parseExp(J, atexps) =
        atExp(parse(appExp, infExp, List.map (categoriseAtExp J) atexps))


  (* Resolving infixed patterns [Section 2.6] *)

  fun atPat(atpat) = ATPat(atpat)@@at(atpat)

  fun conPat(idPat as IDAtPat(op_opt, longvid)@@_, atpat) =
      let
        val conPat = CONPat(op_opt, longvid, atpat)@@over(idPat, atpat)
      in
        PARAtPat(conPat)@@at(conPat)
      end
    | conPat(_, _@@A) =
        error(loc A, "misplaced atomic pattern")

  fun conPat'(idPat as IDAtPat(op_opt, longvid)@@_, atpat) =
      let
          val conPat = INFIXPatX(op_opt, longvid, atpat)@@over(idPat, atpat)
      in
          PARAtPat(conPat)@@at(conPat)
      end
    | conPat'(_, _@@A) = error(loc A, "misplaced atomic pattern")


  fun pairPat(atpat1, atpat2) =
      let
          val patList = [atPat atpat1, atPat atpat2]
      in
          (TUPLEAtPatX patList)@@over(atpat1, atpat2)
      end

  fun infPat(atpat1, IDAtPat(NONE, longvid)@@A, atpat2) =
      conPat'(IDAtPat(NONE, longvid)@@A, pairPat(atpat1, atpat2))
    | infPat(_, _, _) =
        raise Fail "Infix.infPat: inconsistency"

  fun parsePat(J, atpats) =
        atPat(parse(conPat, infPat, List.map (categoriseAtPat J) atpats))


  (* Resolving fun match rules [Figure 21, note] *)

  fun parseFmrule(J, atpats) =
      (* Allowed is the following:
       * (1) <op> vid atpat+
       * (2) (atpat infix_vid atpat) atpat*
       * (3) atpat infix_vid atpat
       *)
      let
        fun checkNonfixity[] = true
          | checkNonfixity(NONFIX(_)::t) = checkNonfixity t
          | checkNonfixity(INFIX(_, vid@@A, _)::t) =
              errorVId(loc A, "misplaced infix identifier ", vid)

        fun maybeNonfixClause ps =
              case List.hd atpats of
                IDAtPat(op_opt, longvid@@A)@@A' =>
                  if not(LongVId.isShort longvid) then
                    errorLongVId(loc A, "misplaced long identifier ", longvid)
                  else if List.length atpats < 2 then
                    error(loc A', "missing function arguments")
                  else
                    ( checkNonfixity ps;        (* including 1st *)
                      (op_opt, LongVId.toId(longvid)@@A, List.tl atpats)
                    )
              | WILDCARDAtPat@@A =>
                  error(loc A, "misplaced wildcard pattern")
              | UNITAtPatX@@A => 
                  error(loc A, "misplaced unit pattern")              
              | SCONAtPat(_)@@A =>
                  error(loc A, "misplaced constant pattern")
              | RECORDAtPat(_)@@A =>
                  error(loc A, "misplaced record pattern")
              | PARAtPat(_)@@A =>
                  error(loc A, "misplaced parenthesised pattern")
              | TUPLEAtPatX(_)@@A =>
                  error(loc A, "misplaced tuple pattern")
              | LISTAtPatX(_)@@A => 
                error(loc A, "misplaced list pattern")


        fun maybeParenthesisedInfixClause ps =
              case List.hd ps of
                NONFIX(PARAtPat(CONPat(NONE, longvid@@A, atpat)@@A')@@_) =>
                  if not(LongVId.isShort longvid) then
                    errorLongVId(loc A, "misplaced long identifier ", longvid)
                  else if not(isInfix J longvid) then
                    error(loc A', "misplaced non-infix pattern")
                  else
                    (* Now, longvid has infix status but is sans `op',
                     * so it can only result from resolving an
                     * appropriate infix construction.
                     *)
                    ( checkNonfixity(List.tl ps);
                      (NONE, LongVId.toId(longvid)@@A, atpat::List.tl atpats)
                    )
              |  NONFIX(PARAtPat(INFIXPatX(NONE, longvid@@A, atpat)@@A')@@_) =>
                 if not(LongVId.isShort longvid) then
                     errorLongVId(loc A, "misplaced long identifier ", longvid)
                 else if not(isInfix J longvid) then
                     error(loc A', "misplaced non-infix pattern")
                 else
                     (* Now, longvid has infix status but is sans `op',
                      * so it can only result from resolving an
                      * appropriate infix construction.
                      *)
                     ( checkNonfixity(List.tl ps);
                       (NONE, LongVId.toId(longvid)@@A, atpat::List.tl atpats)
                     )
              | NONFIX(PARAtPat(ATPat(atpat as PARAtPat(_)@@_)@@_)@@_) =>
                  maybeParenthesisedInfixClause(NONFIX(atpat)::List.tl ps)
              | NONFIX(PARAtPat(pat)@@A) =>
                 error(loc A, "misplaced non-infix pattern")
              | _ =>
                  maybeNonfixClause(ps)

        fun maybePlainInfixClause(ps) =
              case ps of
                [NONFIX(atpat1), INFIX(_, vid, _), NONFIX(atpat2)] =>
                  (NONE, vid, pairPat(atpat1, atpat2)::[])
              | _ =>
                  maybeParenthesisedInfixClause(ps)
      in
        maybePlainInfixClause(List.map (categoriseAtPat J) atpats)
      end
end;
