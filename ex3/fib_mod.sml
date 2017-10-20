fun fib 0 = 0
  | fib 1 = 1
  | fib n = fib (n - 1) + fib (n - 2);

fun f1 n m = (fib n) mod m = 0;

fun f2 n =
  let
    val a = (fib n)
  in
    fn m => a mod m = 0
  end;

val g1 = f1 35;

val g2 = f2 35;

fun g1_5 () = (g1 1, g1 2, g1 3, g1 4, g1 5);

fun g2_5 () = (g2 1, g2 2, g2 3, g2 4, g2 5);
