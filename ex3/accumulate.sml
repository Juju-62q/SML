fun accumulate h z f n =
  if n = 0 then z
  else h (accumulate h z f (n - 1), f n);

fun power n m = 
  if m = 0 then 1
  else n * power n (m - 1);

fun summation f n = accumulate (fn (x, y) => x + y) 0 f n;

fun f1 n = accumulate (fn (x, y) => x + y) 0 (fn x => x) n;

fun f2 n = accumulate (fn (x, y) => x * y) 1 (fn x => x) n;

fun f3 n x = accumulate (fn (x, y) => x + y) 0 (fn k => k * power x k) n;

