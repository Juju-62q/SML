datatype 'a tree = Empty | Node of 'a * 'a tree * 'a tree;
Control.Print.printDepth := 10; 

fun selMax [] = ~65535
 |  selMax [x] = x
 |  selMax (x::xs) = if x > (selMax xs) then x else selMax xs;

fun nodes Empty = 0
 |  nodes (Node(x,L,R)) = 1 + (nodes L) + (nodes R);

fun mapTree f Empty = Empty
 |  mapTree f (Node(x,L,R)) = Node(f x,mapTree f L, mapTree f R);

fun maxTree Empty = NONE
 |  maxTree (Node(x,L,R)) =
  case (Node(x,L,R))
    of (Node(x,Empty,Empty)) => SOME(x)
     | (Node(x,L,Empty)) => SOME(selMax [x, valOf(maxTree L)])
     | (Node(x,Empty,R)) => SOME(selMax [x, valOf(maxTree R)])
     | (Node(x,L,R)) => SOME(selMax [x,valOf(maxTree L) ,valOf(maxTree R)]);
