signature READCNF =
sig
    type instream
    val readCNF : instream -> int * int list array
    val testReadCNF : string -> unit
end

structure ReadCNF : READCNF = struct
local
    open Control
in

type instream = TextIO.instream

(* 入力ストリーム ins から1行読み込む *)
fun readLine ins =
    let
	val lineOpt = TextIO.inputLine ins
    in
	if isSome lineOpt then
	    let
		val line = valOf lineOpt
	    in
		if List.all Char.isSpace (explode line) orelse substring(line,0,1) = "c"
		then 
		    readLine ins
		else
		    line
	    end
	else raise EndOfInput
    end

(* 入力ストリーム ins から節を読み込む *)
(* numv, numc はそれぞれ problem line に記述された命題変数と節の数 *)
(* clArray は節データを格納する配列であり，clArray の各要素は1個の節を表す整数リスト *)
fun readClauses (ins, numv, numc, clArray) =
    let
	fun readCl clid =
	    if clid > numc then
		(Print.printError ("too many clauses\n");
		 raise Error InputError)
	    else
		let
		    val line = readLine ins
		    val tokens = String.tokens Char.isSpace line
		    val intOptList = map Int.fromString tokens
		in
		    if List.all isSome intOptList then
			let
			    val intList = map valOf intOptList
			    val clauseLen = length intList - 1
			    val clause = List.take (intList,clauseLen)
			in
			    if List.last intList <> 0 then
				(Print.printError ("invalid clause: " ^ line);
				 raise Error InputError)
			    else
				((*Print.printIntList intList;*)
				 Array.update(clArray, clid, clause);
				 readCl (clid + 1))
				handle EndOfInput => (Array.update(clArray, clid, clause)) (* EndOfInput例外発生時は count+1 *)
			end
		    else (Print.printError ("invalid clause: " ^ line);
			  raise Error InputError)
		end
    in
	(readCl 0;
	 clArray)
    end

(* 入力ストリーム ins から problem line を読み込み、                *)
(* 命題変数の数と節の数の組を返す                                   *)
fun readPLine ins =
    let
	val line = readLine ins
	val hl = String.tokens Char.isSpace line
    in
	if length hl <> 4 then
	    (Print.printError "invalid problem line\n";
	     raise Error InputError)
	else
	    let
		val nvo = Int.fromString (List.nth (hl,2))
		val nco =  Int.fromString (List.nth (hl,3))
		val v = if isSome nvo then
			    valOf nvo
			else
			    (Print.printError "invalid number of variables\n";
			     raise Error InputError)
		val c = if isSome nco then
			    valOf nco
			else
			    (Print.printError "invalid number of clauses\n";
			     raise Error InputError)
	    in
		((*print ("Variables: " ^ (Int.toString v) ^ " Clauses: " ^ (Int.toString c) ^ "\n");*)
		 (v,c))
	    end
    end

(* 入力ストリーム ins から CNF ファイルの内容を読み込む *)
fun readCNF ins =
    let
	val (numv,numc) = readPLine ins
	val cla = Array.array(numc,[])
	val clArray = readClauses (ins, numv, numc, cla)
	val nc = Array.length clArray
    in
	(* numc は problem line で宣言された節の数 *)
	(* nc はCNFファイルに記述された節の数 *)
	if (nc <> numc) then
	    (Print.printError "number of clauses is invalid\n";
	     Print.printError ((Int.toString nc) ^ " clauses are found\n");
	     raise Error InputError)
	else 
	    (numv, clArray)
    end
    
(* ファイル名 fname のファイルからCNF ファイルを読み込む *)
(* 動作確認用関数 *)
fun testReadCNF fname =
    let
	val ins = TextIO.openIn fname
	val (numv, clArray) = readCNF ins
				      
    in
	TextIO.closeIn ins
    end
    
end
end
