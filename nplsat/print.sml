signature PRINT =
sig
    val printError : string -> unit
    val printIntList : int list -> unit
    val printIntListList : int list list -> unit
    val printStringList : string list -> unit
    val printIntArray : int array -> unit
    val printIntListArray : int list array -> unit
    val printStrInt : string -> int -> unit
    val printStrIntInf : string -> IntInf.int -> unit
    val printStrIntNonl : string -> int -> unit
    val printBoolArray : bool array -> unit
    val printResult : TextIO.outstream -> int list -> unit
end

structure Print : PRINT =
struct
local 
      open Array TextIO
in

(* メッセージを標準エラー出力に出力する *)
fun printError s = output(stdErr,s)

(* 整数のリストを標準出力に出力 *)
fun printIntListElem [] = print ""
  | printIntListElem [h] = print ((Int.toString h))
  | printIntListElem (h :: t) = (print ((Int.toString h) ^ ",");
			     printIntListElem t
			     )
fun printIntList l = (print "[";printIntListElem l;print "]\n")

(* 整数のリストのリストを標準出力に出力 *)
fun printIntListListElem [] = print ""
  | printIntListListElem (h :: t) = (print "[";
				     printIntListElem h;
				     print "]";
				     printIntListListElem t
				     )
fun printIntListList l = (print "[";printIntListListElem l;print "]\n")

(* 整数の配列を標準出力に出力 *)
fun printIntArray ar =
    let
	val size = length(ar)
	fun prArrayN k =
	    if k < size - 1 then
		(print (Int.toString(sub(ar,k)) ^ ",");
		 prArrayN (k+1)
		 )
	    else 
		if k < size then
		    print (Int.toString(sub(ar,k)))
		else print ""
    in
	(print "[|";
	 prArrayN 0;
	 print "|]\n"
	 )
    end

(* 真理値の配列を標準出力に出力 *)
fun printBoolArray ar =
    let
	val size = length(ar)
	fun boolString b = if b then "True" else "False"
	fun prArrayN k =
	    if k < size - 1 then
		(print (boolString(sub(ar,k)) ^ ",");
		 prArrayN (k+1)
		 )
	    else 
		if k < size then
		    print (boolString(sub(ar,k)))
		else print ""
    in
	(print "[|";
	 prArrayN 0;
	 print "|]\n"
	 )
    end

(* 整数のリストの配列を標準出力に出力 *)
fun printIntListArray ar =
    let
	val size = length(ar)
	fun prListArrayN k =
	    if k < size - 1 then
		(print "[";
		 printIntListElem (sub(ar,k));
		 print "],";
		 prListArrayN (k+1)
		 )
	    else 
		if k < size then
		    (print "[";
		     printIntListElem (sub(ar,k));
		     print "]"
		     )
		else print ""
    in
	(print "[|";
	 prListArrayN 0;
	 print "|]")
    end

(* 文字列のリストの要素をコンマで区切って標準出力に出力 *)
fun printStringList [] = ()
  | printStringList [h] = (print h; print "\n")
  | printStringList (h :: t) = (print h; print ","; printStringList t)

(* 文字列，整数を標準出力に出力 *)
fun printStrInt s i = print (s ^ (Int.toString i) ^ "\n")

(* 文字列，IntInf を標準出力に出力 *)
fun printStrIntInf s i = print (s ^ (IntInf.toString i) ^ "\n")

(* 文字列，整数を標準出力に出力し、改行せず *)
fun printStrIntNonl s i = print (s ^ (Int.toString i) ^ " ")

(* 整数を文字列に変換 *)
(* 負号を "-" にする  *)
fun intToString n = 
    if n < 0 then "-"^(Int.toString(~n)) 
    else Int.toString n

(* 変数の割り当てを表示 *)
(* 最後に 0 を出力      *)
fun printResult outs rl =
    let
	fun pr [] k = output (outs, "0\n")
	  | pr (h :: t) k =
	    (output (outs, intToString(h * k));
	     output (outs, " ");
	     pr t (k+1))
    in
	pr rl 1
    end

(* 節の変数割り当てを出力 *)
fun printClauseValue cl vval =
    let
	val cllen = length cl
	fun pcv  cl n =
	    if n >= cllen then print "\n"
	    else
		let
		    val v = sub(cl,n)
		    val vid = abs v
		    val vv = sub(vval, vid)
		in
		    (print ((Int.toString vid) ^ ":" ^ (Int.toString vv) ^ " ");
		     pcv cl (n+1))
		end
    in
	pcv cl 0
    end

end

end
