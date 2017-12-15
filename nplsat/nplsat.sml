structure Nplsat = struct
local
    open Control
in

(* 引数を調べて関数を呼び出す *)
fun scan args =
    let
	(* args の先頭要素を入力ファイル名とする *)
	val ifilename = hd args
	val ins = TextIO.openIn ifilename
	(* args の2番めの要素を出力ファイル名とする *)
	val ofilelist = tl args
	(* 出力ファイル名が指定されていない場合は出力ストリームを標準出力に *)
	val noOutputFile = null ofilelist
	val outs = if noOutputFile then TextIO.stdOut
		   else TextIO.openOut (hd (ofilelist))
	val (numv, clauses) = ReadCNF.readCNF ins
	val result = Solver.solve (numv, clauses)
    in
	(TextIO.closeIn ins;
	 TextIO.flushOut TextIO.stdOut;
	 (
	   Print.printStrIntInf "Decisions: " (!Solver.numDecisions);
	   Print.printStrIntInf "Conflicts: " (!Solver.numConflicts);
	   Print.printStrIntInf "Implications: " (!Solver.numImplications);
	   case result of 
	       SOME(res) =>
               (print "SATISFIABLE\n";
		if noOutputFile then Print.printResult outs res
		else (TextIO.output (outs, "SAT\n");
		      Print.printResult outs res)
	       )
	      |NONE =>
               (print "UNSATISFIABLE\n";
		if noOutputFile then ()
		else TextIO.output (outs, "UNSAT\n")
	       )
	 );
	 if noOutputFile then ()
	 else TextIO.closeOut (outs)
	)
    end


fun timer args =
    let
	(* プロセス開始後にプログラムが使用したCPU時間(ミリ秒)を取得する関数 *)
	fun utime () = IntInf.toInt(Time.toMilliseconds(#usr(Timer.checkCPUTimer(Timer.totalCPUTimer()))))
	(* 現在までに使用したCPU時間を starttime に保存 *)
	val starttime = utime ()
	val _ = scan args
	val comptime = (utime ()) - starttime
    in
	(print "Computation time is ";
	 print (Int.toString comptime);
	 print "msec.\n")
    end	    
	    
fun nplsat(name : string, args : string list) =
    let
	val usage = "USAGE: sat <input-file> [<result-ouput-file>]"
	fun dosat args = if (null args) orelse (hd args) = "--help"
                          then Print.printError (usage ^ "\n")
                          else timer args
    in (dosat args; OS.Process.success) 
       handle Error(no)=> OS.Process.failure
    end
	
end

end
