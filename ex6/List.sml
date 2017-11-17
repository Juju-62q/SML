fun sumList [] = 0
 |  sumList (x::xs) = x + (sumList xs);

fun member key [] = false
 |  member key (x::xs) = 
  if key = x then
    true
  else
    member key xs;

fun unique [] = []
 |  unique (x::xs) = 
  if member x xs then
    unique xs
  else
    x::(unique xs);
  
fun filter f [] = []
 |  filter f (x::xs) =
  if f x then
    x::(filter f xs)
  else
    filter f xs;   
