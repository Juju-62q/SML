fun length [] = 0
 |  length (x::xs) = 1 + length xs;

fun isPrefix x y =
  let
    val xLen = length (explode x)
    val yLen = length (explode y)
  in
    if xLen > yLen then
      false
    else if x = substring(y,0,xLen) then
      true
    else
      false
  end;

