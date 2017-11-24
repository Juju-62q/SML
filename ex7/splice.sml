fun splice ([], pre) = ""
 |  splice ((x::[]), pre) = x
 |  splice ((x::xs), pre) = x^pre^splice (xs, pre);
