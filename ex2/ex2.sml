fun fib 0 = 0
  | fib 1 = 1
  | fib n = fib(n - 1) + fib(n - 2);

fun twofib 0 = (0, 1)
  | twofib n = 
    let 
      val (t1,t2) = twofib(n - 1)
    in
      (t2, t2 + t1)
    end;
