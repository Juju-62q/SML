fun suffixList [] = [[]]
 |  suffixList (x::xs) = (x::xs)::suffixList xs;

fun suffixListFr L = foldr (fn (x, y::ys) => (x::y)::(y::ys)) [[]] L;
