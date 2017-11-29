datatype 'a tree = Empty | Node of 'a * 'a tree * 'a tree;
Control.Print.printDepth := 10; 

fun fromPreOrder s =
  let fun decompose s =
    let
      fun searchLP s p =
        if substring(s,p,1)="(" then 
          p
        else
          searchLP s (p+1)
    
      fun searchRP s p n =
        case (substring(s,p,1),n)
          of (")",0) => p
           | (")",n) => searchRP s (p+1) (n-1)
           | ("(",n) => searchRP s (p+1) (n+1)
           | (_,n) => searchRP s (p+1) n
  
      val lp1 = searchLP s 0
      val rp1 = searchRP s (lp1+1) 0
      val lp2 = searchLP s (rp1+1)
      val rp2 = searchRP s (lp2+1) 0
    in
      (substring (s,0,lp1),
      substring (s,lp1+1,rp1-lp1-1),
      substring (s,lp2+1,rp2-lp2-1))
    end
  in if s = "" then Empty
     else let val (root,left,right) = decompose s
        in Node(root, fromPreOrder left, fromPreOrder right)
        end
  end;

fun nodes Empty = 0
 |  nodes Node(x,L,R) = 1 + (nodes L) + (nodes R);

