(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML label identifiers and maps thereof
 *
 * Definition, Sections 2.4 and 4.2
 *)

structure Lab :> LAB =
struct
    (* Type [Section 2.4] *)

    type Lab = string					(* [lab] *)


    (* Conversions *)

    fun fromString s = s
    val fromInt      = Int.toString
    fun toString s   = s


    (* Ordering *)

    fun compare(lab1,lab2) =
	(case (Int.fromString lab1, Int.fromString lab2)
	   of (SOME i1, SOME i2) => Int.compare(i1,i2)
	    |     _              => String.compare(lab1,lab2)
	) handle Overflow => String.compare(lab1,lab2)
end

structure LabSet = FinSetFn(type ord_key = Lab.Lab
			    val  compare = Lab.compare);
structure LabMap = FinMapFn(type ord_key = Lab.Lab
			    val  compare = Lab.compare);
