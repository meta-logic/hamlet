(!! 
	add x y z ==> (b:int);
	REQUIRES: true;
	ENSURES: b <> x + y + z; 
!!)
fun bad_add (x) q 0 = x + q 
  | bad_add (x) z _ = z ;  

fun trueLen [] =0
  | trueLen (a::l) = 1 + trueLen l


(!! 
	len l ==> result;
	REQUIRES: (List.length l) >= 0;
	ENSURES: result = (trueLen l); 
!!)
fun len (x::l') = 1 + len l'
  | len [] = 0;
