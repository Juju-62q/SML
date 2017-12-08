Control.Print.printDepth := 10;
Control.Print.stringDepth := 100;
Control.Print.printLength := 100;

fun swap (array, i, k) =
  let
    val tmp = Array.sub(array, i)
  in
    (Array.update(array, i, Array.sub(array, k)); Array.update(array, k, tmp))
  end;

fun partition (array, p, a, b) =
  let
    val av = Array.sub(array, a);
    val bv = Array.sub(array, b);
  in
    case ( b <= a, av <= p, p < bv)
      of (true, _, _) =>
        if av <= p then a else a - 1
       | (_, true, _) =>
        partition (array, p, a + 1, b)
       | (_, _, true) =>
        partition (array, p, a, b - 1)
       | (_, _, _) =>
        (swap(array, a, b); partition(array, p, a + 1, b - 1))
  end;

fun qsort (array, i, k) =
  if k <= i then ()
  else
    let
      val pivot = Array.sub(array, i);
      val pvPos = partition(array, pivot, i + 1, k);
      val _ = swap(array, i, pvPos);
    in
      (qsort (array, i, pvPos - 1); qsort (array, pvPos + 1, k))
    end

fun sort (array) =
  qsort (array, 0, Array.length(array) - 1);

fun fixedSeq (m,n) =
  let
    val seed = (Random.rand (0,1))
    fun randomI() = (Random.randInt seed) mod m
  in
    Array.tabulate (n, fn x=>randomI())
  end

fun sortedList 0 = []
 |  sortedList m = (sortedList (m - 1))@[m];

val sortedArray = Array.fromList (sortedList 50000);

val randArray = fixedSeq(50,50000);

fun qsort' (array, i, k) =
  if k <= i then ()
  else
    let
      val _ = swap(array, 0, (i + k) div 2);
      val pivot = Array.sub(array, 0);
      val pvPos = partition(array, pivot, i + 1, k);
      val _ = swap(array, i, pvPos);
    in
      (qsort (array, i, pvPos - 1); qsort (array, pvPos + 1, k))
    end

fun sort' (array) =
  qsort' (array, 0, Array.length(array) - 1);

fun arrayToList arr = Array.foldr (op ::) [] arr;

fun checkAscFromList [] key = true
 |  checkAscFromList (x::xs) key = 
  if x >= key then
    checkAscFromList xs x
  else
    false;

fun checkAsc (array) = (checkAscFromList (arrayToList(array)) (Array.sub(array, 0)));
