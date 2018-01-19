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

	(* ̿���ѿ���������� *)
	val varValues =  array(vasize, 0)
	val varDecLevel =  array(vasize, ~1)
	val varFlipped = array(vasize, false)
	val varClT = array(vasize, []) : int list array
	val varClF = array(vasize, []) : int list array
					  
	(* ����������� *)
	val clNumF =  array(numClauses,0)
	val clNumT =  array(numClauses,0)

	(* ������ƥ����å������� *)
	val assignStack = array(vasize, []) : int list array

	(* varClT, varClF ���ͷ׻� *)
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

	(* ̿���ѿ�����(Decision)��Ԥ� *)
	fun decideLoop count =
	    if count <= numVariables then
		if sub(varValues,count) = 0 then
		    count
		else
		    decideLoop (count+1)
	    else
		0;

	fun decide () =
	    let
		(* numDecisions ��1���䤹 *)
		val _ = numDecisions := !numDecisions + 1
		val decidenum = decideLoop 1
	    in 
		if(decidenum = 0) then
		    NONE
		else
		    (update(varFlipped,decidenum,false);SOME([~decidenum]))
	    end
	(* ID �� vid �Ǥ���̿���ѿ����� sign �������Ƥ� *)
	fun setVarValue (vid, sign) =
	    let
		(* numImplications ��1���䤹 *)
		val _ =  numImplications := !numImplications + 1
		(* varValues �򹹿����� *)
		val _ = update (varValues, vid, sign)
			       
		(* clT ��̿���ѿ� vid ������ƥ��Ȥ��Ƹ������ꥹ�� *)
		val clT = sub (varClT, vid)
		(* clF ��̿���ѿ� vid �����ƥ��Ȥ��Ƹ������ꥹ�� *)
		val clF = sub (varClF, vid)
		(* ������clID�Υꥹ�Ȥ����ꡢ����� clNumT ��1���䤹�� *)
		(* clNumT �ϳ���ο���ƥ��ο��Ǥ��롣                 *)
		fun incrClNumT nil = ()
		  | incrClNumT (cl::t) =
		    let
			val newct = sub (clNumT, cl) + 1
			val _ = update (clNumT, cl, newct)
		    in
			incrClNumT t
		    end
		(* ������clID�Υꥹ�Ȥ����ꡢ����� clNumF ��1���䤹��     *)
		(* clNumF �ϳ���ε���ƥ��ο��Ǥ��롣                     *)
		(* �ޤ���clNumF ���ͤ���Υ�����(��ƥ��ο�)���������ʤä� *)
		(* ���ϥꥹ�� conflicts ��������clID��ä��롣             *)
		fun incrClNumF nil conflicts = conflicts
		  | incrClNumF (cl::t) conflicts =
		    let
			val newcf = sub (clNumF, cl) + 1
			val _ = update (clNumF, cl, newcf)
		    in
			if(sub(clNumF,cl) >= (List.length(sub(clLiterals,cl)))) then
			       cl::(incrClNumF t conflicts)
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
		
	(* ID �� vid �Ǥ���̿���ѿ��γ�����Ƥ���ä� *)
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
		
	(* ����(Deduction)��Ԥ� *)
	(* deduce �� setVarValues ���֤��͡�conflicts�ˤ��֤� *)
	fun deduce implicationQueue decLevel =
	    let
		fun deduceQueue [] = []
		  | deduceQueue (assignVal :: rest) =
		    let
			(* ̿���ѿ�ID *)
			val vid = abs assignVal
			(* ������Ƥ���(���ΤȤ���1, ���ΤȤ��� -1) *)
			val value = Int.sign assignVal
		    in
			(* �ͤ�̤��Ǥ���̿���ѿ��Τߤ��ͳ�����Ƥ�Ԥ� *)
			if (sub (varValues, vid) = 0) then
			    let
				(* varDecLevel, assignStack �ι����򤹤� *)
				val _ = update(varDecLevel,vid,decLevel)
				val _ = update(assignStack,decLevel,((sub(assignStack,decLevel))@[assignVal]))
				val conflicts = setVarValue (vid, value)
			    in
				Print.printStrIntNonl "setVarValue " vid;
				Print.printStrInt "" value;
				print "varValues: ";
				Print.printIntArray (varValues);
				print "clNumT: ";
				Print.printIntArray (clNumT); print "clNumF: ";
				Print.printIntArray (clNumF); print "conflicts: ";
				Print.printIntList (conflicts);
				(* conflicts �����ξ��ΤߺƵ���³���� *)
				if null conflicts then deduceQueue rest else conflicts
			    end
			else
			    (* ̿���ѿ����ͤ�̤��Ǥʤ����� deduceQueue �κƵ��ƤӽФ���Ԥ� *)
			    deduceQueue rest
		    end
	    in
		deduceQueue implicationQueue
	    end
		
	(* ̷��β���(Conflict-analysis)��Ԥ� *)
	(* conflicts �ϻ��Ѥ��Ƥ��ʤ� *)
	fun analyzeConflicts decLevel conflicts =
	    let
		(* numConflicts ��1���䤹 *)
		val _ = numConflicts := !numConflicts + 1
		fun flipVar 0 = (0, [])
		  | flipVar n =
			flipVar (n - 1)
	    in
		flipVar decLevel
	    end
		
	(* decLevel �ʲ���backLevel �ʾ�γ�����Ƥ���ä� *)
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
		
	(* õ���ڤˤ����Ƽ��λޤν�����Ԥ� *)
	fun nextBranch decLevel =
	    let
		val iqueueOpt = decide ()
		(* �ͳ�����Ƥ�Ԥ� *)
		(* ���� Decision Level ���֤� *)
		(* Unsatisfialble �ʤ� 0 ���֤� *)
		fun assignValue implicationQueue decLevel =
		    let
	val _ = Print.printStrInt "deduce at decision level " decLevel; val _ = print "implicationQueue: "; val _ = Print.printIntList implicationQueue;
			val conflicts = deduce implicationQueue decLevel
val _ = print "varDecLevel: "; val _ = Print.printIntArray varDecLevel; val _ = Print.printStrIntNonl "assignStack at decision level " decLevel; val _ = Print.printIntList (sub(assignStack,decLevel));
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
(*
			val _ = Print.printStrInt "decLevel: " decLevel 
			val _ = print "implicationQueue: " 
			val _ = Print.printIntList implicationQueue
*)
			val newDecLevel = assignValue implicationQueue decLevel
		    in
			if newDecLevel > 0
			then nextBranch (newDecLevel+1)
			else false
		    end
		else
		    true (* ���򤹤������ѿ����ʤ���� SATISFIABLE *)
	    end
		
	(* ��®���Τ������������Ԥ� *) 
	fun preprocess () =
	    let
		(* ��������ID *)
		fun findUnitClauses n = []
		val unitClauses = findUnitClauses 0
		(* unitClauses ���Ф��ƿ�����Ԥ� *)
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
