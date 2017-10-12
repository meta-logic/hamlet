(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML overloading classes
 *
 * Definition, Appendix E
 *
 * Note:
 *  Overloading -- and defaulting in particular -- is not well formalised in
 *  the Definition. We treat overloaded constants and identifiers
 *  uniformingly and tried to smoothly integrate overloading resolution into
 *  type inference by generalising the concept of overloading class a bit.
 *  We describe an overloading class as a pair (T,t) of a set
 *  of type names (like the definition does), plus the default type name t.
 *  For overloading to be sound some well-formedness properties have to be
 *  enforced for all existing overloading classes (T,t):
 *  (1) t elem T
 *  (2) Eq T = 0  \/  t admits equality
 *  (3) forall (T',t') . (TT' = 0  \/  |{t,t'} intersect TT'| = 1)
 *  where Eq T = {t elem T | t admits equality} and we write TT' for
 *  T intersect T' and 0 for the empty set.
 *  The reason for (1) is obvious. (2) guarantees that we do not loose the
 *  default if we enforce equality. (3) ensures a unique default whenever we
 *  have to unify two overloading classes. (2) and (3) also allow the
 *  resulting set to become empty which represents a type error.
 *)

signature OVERLOADINGCLASS =
sig
    (* Import *)

    type TyName    = TyName.TyName
    type TyNameSet = TyNameSet.set


    (* Type *)

    type OverloadingClass				(* [O] *)


    (* Operations *)

    val make :		TyNameSet * TyName -> OverloadingClass

    val isEmpty :	OverloadingClass -> bool
    val set :		OverloadingClass -> TyNameSet
    val member :	OverloadingClass * TyName -> bool
    val default :	OverloadingClass -> TyName

    val makeEquality :	OverloadingClass -> OverloadingClass option
    val intersection :	OverloadingClass * OverloadingClass ->
					   OverloadingClass option
    val union :		OverloadingClass * OverloadingClass ->
					   OverloadingClass
end;
