fun S1 1 = 1
  | S1 n = n + S1(n - 1);
  
fun S2 1 = S1(1)
  | S2 n = S1 n + S2(n - 1); 
