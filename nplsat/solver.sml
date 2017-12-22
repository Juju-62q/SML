signature SOLVER = sig
    val numDecisions : IntInf.int ref
    val numConflicts : IntInf.int ref
    val numImplications : IntInf.int ref

    val solve : int * int list array -> int list option
end

structure Solver : SOLVER = struct
local
    open Array Control
in

val numDecisions = ref (0 : IntInf.int)
val numConflicts = ref (0 : IntInf.int)
val numImplications = ref (0 : IntInf.int)

fun arrayToList ar =
    let
	val alen = length ar
	fun a2l ar k =
	    if k >= alen then []
	    else sub(ar, k) :: a2l ar (k + 1)
    in
	a2l ar 0
    end

fun printCNF (nv, clArray) =
    let
	val nc = Array.length clArray
	fun pcnf n =
	    if n >= nc then ()
	    else
		(Print.printIntList (Array.sub(clArray,n));
		 pcnf (n+1))
    in
	(Print.printStrInt "Number of variables = " nv;
	 Print.printStrInt "Number of clauses = " nc;
	 pcnf 0)
    end

fun solve (numVariables, clLiterals) =
    let
	val numClauses = length clLiterals
	val vasize = numVariables + 1

	(* 命題変数配列の生成 *)
	val varValues =  array(vasize, 0)
	val varDecLevel =  array(vasize, ~1)
	val varFlipped = array(vasize, false)
	val varClT = array(vasize, []) : int list array
	val varClF = array(vasize, []) : int list array
					  
	(* 節配列の生成 *)
	val clNumF =  array(numClauses,0)
	val clNumT =  array(numClauses,0)

	(* 割り当てスタックの生成 *)
	val assignStack = array(vasize, []) : int list array

	(* varClT, varClF の値計算 *)
	fun makeVarCl clid =
	    let
		fun mkVarCl1 [] = ()
		  | mkVarCl1 (literal :: rest) =
		    let
			val vid = abs(literal)
		    in
			(if literal > 0 then
			     update (varClT, vid, sub (varClT, vid) @ [clid])
			 else
			     update (varClF, vid, sub (varClF, vid) @ [clid]);
			 mkVarCl1 rest)
		    end
	    in
		if clid >= numClauses then ()
		else
		    let
			val clause = sub (clLiterals, clid)
		    in
			(mkVarCl1 clause;
			 makeVarCl (clid + 1))
		    end
	    end

	fun initVariables () = (
	    numDecisions := 0;
	    numConflicts := 0;
	    numImplications := 0;
	    makeVarCl 0
	)

	fun decideLoop count =
        if count <= numVariables then
		    if (sub (varValues, count)) = 0 then
                count
		    else
                decideLoop (count + 1)
        else
		    0

	(* 命題変数選択(Decision)を行う *)
	fun decide () =
	    let
		(* numDecisions を1増やす *)
		    val _ = numDecisions := !numDecisions + 1
            val variableId = (decideLoop 1)
	    in
            if variableId = 0 then
                NONE
            else
                (update (varFlipped, variableId, false);SOME([~variableId]))
	    end

	(* ID が vid である命題変数に値 sign を割り当てる *)
	fun setVarValue (vid, sign) =
	    let
		(* numImplications を1増やす *)
		val _ =  numImplications := !numImplications + 1
		(* varValues を更新する *)
		val _ = update (varValues, vid, sign)
			       
		(* clT は命題変数 vid が正リテラルとして現れる節リスト *)
		val clT = sub (varClT, vid)
		(* clF は命題変数 vid が負リテラルとして現れる節リスト *)
		val clF = sub (varClF, vid)
		(* 引数にclIDのリストを受取り、各節の clNumT を1増やす。 *)
		(* clNumT は各節の真リテラルの数である。                 *)
		fun incrClNumT nil = ()
		  | incrClNumT (cl::t) =
		    let
			val newct = sub (clNumT, cl) + 1
			val _ = update (clNumT, cl, newct)
		    in
			incrClNumT t
		    end
		(* 引数にclIDのリストを受取り、各節の clNumF を1増やす。     *)
		(* clNumF は各節の偽リテラルの数である。                     *)
		(* また、clNumF の値が節のサイズ(リテラルの数)と等しくなった *)
		(* 場合はリスト conflicts の末尾にclIDを加える。             *)
		fun incrClNumF nil conflicts = conflicts
		  | incrClNumF (cl::t) conflicts =
		    let
			    val newcf = sub (clNumF, cl) + 1
			    val _ = update (clNumF, cl, newcf)
		    in
                if (sub (clNumF, cl)) >= (length clLiterals) then
                    incrClNumF t (cl::conflicts)
                else
			        incrClNumF t conflicts
		    end
	    in
		if sign > 0 then (incrClNumT clT;
				  incrClNumF clF [])
		else if sign < 0 then (incrClNumT clF;
				       incrClNumF clT [])
		else (Print.printError "Invalid value to assign.\n";
		      raise Error UnexpectedError)
	    end
		
	(* ID が vid である命題変数の割り当てを取り消す *)
	fun unsetVarValue vid =
	    let
		val sign = sub (varValues, vid)
		val clT = sub (varClT, vid)
		val clF = sub (varClF, vid)
		val _ = update (varValues, vid, 0)
		fun decrClNumT nil = ()
		  | decrClNumT (cl::t) =
		    let
			val newct = sub (clNumT, cl) - 1
			val _ = update (clNumT, cl, newct)
		    in
			decrClNumT t
		    end
		fun decrClNumF nil = ()
		  | decrClNumF (cl::t) =
		    let
			val newcf = sub(clNumF, cl) - 1
			val _  = update(clNumF, cl, newcf)
		    in
			decrClNumF t
		    end
	    in
		if sign > 0 then (decrClNumT clT;
				  decrClNumF clF)
		else if sign < 0 then (decrClNumT clF;
				       decrClNumF clT)
		else (Print.printError "Invalid value to un-assign.\n";
		      raise Error UnexpectedError)
	    end
		
	(* 推論(Deduction)を行う *)
	(* deduce は setVarValues の返す値（conflicts）を返す *)
	fun deduce implicationQueue decLevel =
	    let
		fun deduceQueue [] = []
		  | deduceQueue (assignVal :: rest) =
		    let
			(* 命題変数ID *)
			val vid = abs assignVal
			(* 割り当てる値(真のときは1, 偽のときは -1) *)
			val value = Int.sign assignVal
		    in
			(* 値が未定である命題変数のみに値割り当てを行う *)
			if (sub (varValues, vid) = 0) then
			    let
				(* varDecLevel, assignStack の更新をする *)
				val conflicts = setVarValue (vid, value)
			    in
                    Print.printStrIntNonl "setVarValue " vid; 
                    Print.printStrInt "" value; 
                    print "varValues: "; 
                    Print.printIntArray (varValues); 
                    print "clNumT: "; 
                    Print.printIntArray (clNumT); 
                    print "clNumF: "; 
                    Print.printIntArray (clNumF); 
                    print "conflicts: "; Print.printIntList (conflicts);
				(* conflicts が空の場合のみ再帰を続ける *)
				if null conflicts then deduceQueue rest else conflicts
			    end
			else
			    (* 命題変数の値が未定でない場合も deduceQueue の再帰呼び出しを行う *)
			    deduceQueue rest
		    end
	    in
		deduceQueue implicationQueue
	    end
		
	(* 矛盾の解析(Conflict-analysis)を行う *)
	(* conflicts は使用していない *)
	fun analyzeConflicts decLevel conflicts =
	    let
		(* numConflicts を1増やす *)
		val _ = numConflicts := !numConflicts + 1
		fun flipVar 0 = (0, [])
		  | flipVar n =
			flipVar (n - 1)
	    in
		flipVar decLevel
	    end
		
	(* decLevel 以下、backLevel 以上の割り当てを取り消す *)
	fun backtrack backLevel decLevel =
	    let
		fun bt n =
		    if (n < backLevel) then ()
		    else
			let
			    val assignedAtDecLevel = sub (assignStack, n)
			    fun usetvar nil = update(assignStack, n, [])
			      | usetvar (h :: t) =
				let
				    val vid = abs h
				in
				    (unsetVarValue vid;
				     update (varDecLevel, vid, ~1);
				     usetvar t
				    )
				end
			    val _ = usetvar assignedAtDecLevel
			in
			    bt (n-1)
			end
	    in
		bt decLevel
	    end
		
	(* 探索木において次の枝の処理を行う *)
	fun nextBranch decLevel =
	    let
		val iqueueOpt = decide ()
		(* 値割り当てを行う *)
		(* 次の Decision Level を返す *)
		(* Unsatisfialble なら 0 を返す *)
		fun assignValue implicationQueue decLevel =
		    let
			val conflicts = deduce implicationQueue decLevel
		    in
			if null conflicts  then
			    decLevel
			else
			    let
				val (backLevel, newImplicationQueue) = analyzeConflicts decLevel conflicts
			    in
				if backLevel = 0 then 0
				else (backtrack backLevel decLevel;
				      assignValue newImplicationQueue backLevel
				     )
			    end
		    end
	    in
		if isSome iqueueOpt then
		    let
			val implicationQueue = valOf iqueueOpt
            val _ = Print.printStrInt "decLevel: " decLevel 
            val _ = print "implicationQueue: " 
            val _ = Print.printIntList implicationQueue
			val newDecLevel = assignValue implicationQueue decLevel
		    in
			if newDecLevel > 0
			then nextBranch (newDecLevel+1)
			else false
		    end
		else
		    true (* 選択する論理変数がなければ SATISFIABLE *)
	    end
		
	(* 高速化のための前処理を行う *) 
	fun preprocess () =
	    let
		(* 引数は節ID *)
		fun findUnitClauses n = []
		val unitClauses = findUnitClauses 0
		(* unitClauses に対して推論を行う *)
		val conflicts = deduce unitClauses 0
	    in
		null conflicts
	    end
		
    in
	(initVariables ();
	 printCNF(numVariables, clLiterals);
         if preprocess () then
	     if nextBranch 1 then (SOME (tl (arrayToList varValues)))
	     else NONE
	 else NONE)
    end
	
end
end
