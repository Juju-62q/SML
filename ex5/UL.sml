fun upperChar [] = []
  | upperChar (x::xs) = Char.toUpper x :: upperChar xs;

fun upper x = implode (upperChar (explode x));

fun lowerChar [] = []
  | lowerChar (x::xs) = Char.toLower x :: lowerChar xs;

fun lower x = implode (lowerChar (explode x));
