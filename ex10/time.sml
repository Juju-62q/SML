fun time f arg =
    let
	val timer = Timer.startCPUTimer()
	val result = f arg
    in
	print (Real.toString(Time.toReal(#usr(Timer.checkCPUTimer timer))));
	print " sec.\n";
	result
    end;
