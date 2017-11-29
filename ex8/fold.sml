datatype 'a tree = Empty | Node of 'a * 'a tree * 'a tree;
Control.Print.printDepth := 10; 

fun treeFold f z Empty = z
 |  treeFold f z (Node(x,L,R)) = f (x, treeFold f z L, treeFold f z R);

fun nodes T = treeFold (fn (x,rL,rR) => 1 + rL + rR ) 0 T;

fun mapTree f T = treeFold (fn (x,rL,rR) => Node(f x,rL,rR)) Empty T;
