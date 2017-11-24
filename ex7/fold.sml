fun flattenFr L = foldr (fn (h,R) => h@R) [] L;

fun forallFr f L = foldr (fn (h,R) => (f h) andalso R ) true L;

fun revFl L = foldl (fn (h,R) => h::R) [] L;
