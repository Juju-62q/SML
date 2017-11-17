fun absList [] = []
 |  absList (x::xs) =
  if x < 0 then
    (~x)::absList xs
  else
    x::absList xs;

fun isNum x = (Char.isAlphaNum x) andalso (not (Char.isAlpha x));

fun getUpperOrNumFromList [] = []
 |  getUpperOrNumFromList (x::xs) =
  if isNum x orelse Char.isUpper x then
    x::(getUpperOrNumFromList xs)
  else
    getUpperOrNumFromList xs;

fun abbreviate s = implode (getUpperOrNumFromList (explode s));
  
