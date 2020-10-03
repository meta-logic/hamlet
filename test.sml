(!! 
	REQUIRES: x >= 0;
	ENSURES: result = x; 
!!)
fun add (x:int) y 0: int = x + y 
  | add (x:int) z _: int = z ;  


(!! 
	REQUIRES: (List.length l') + 1  > 0;
	ENSURES: result = x; 
!!)
fun len (x::l') = 1 + len l'
  | len [] = 0;