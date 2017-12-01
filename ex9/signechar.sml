signature LONGNAT = sig
  exception NegativeLongNat
  exception IllegalLongNat
  type longnat

  val fromIntList : int list -> longnat
  val toString : longnat -> string
  val inc : longnat -> longnat
  val dec : longnat -> longnat
  val add : longnat * longnat -> longnat
end

structure LongNat :> LONGNAT = struct
exception NegativeLongNat
exception IllegalLongNat
type longnat = int list

  (* 各要素の最大値 *)
  val emax = 9999
  (* 各要素の最大桁数 = size (Int.toString emax) *)
  val edigit = 4

  (* int list から longnat を生成する *)
  fun fromIntList [0] = []
   |  fromIntList l = 
    if List.all (fn x => x >=0 andalso x <= emax) l then l
    else raise IllegalLongNat

  (* longnat を文字列に変換する *)
  fun toString lnat =
    if null lnat then "0" 
    else
      let
        val revlnat = rev lnat
        (* "0" を追加して桁をそろえる *)
        fun padding0 x =
          let
            val xstr = Int.toString x
            val num0 = edigit - (size xstr)
            fun numstring (n,s) = 
              if n < 1 then ""
              else s ^ (numstring (n - 1, s))
          in
            numstring(num0, "0") ^ xstr
          end
      in
        Int.toString (hd revlnat) ^ concat (map padding0 (tl revlnat))
      end
    (* 関数 inc, dec, add の定義を追加する *)
  fun inc [] = [1]
   |  inc (x::xs) =
    if x = emax then
      0::(inc xs)
    else 
      (x + 1)::xs

  fun dec [] = raise NegativeLongNat
   |  dec [1] = []
   |  dec (x::xs) =
    if x = 0 then
      emax::(dec xs)
    else
      (x - 1)::(xs)

  fun addc ([], [], 0) = []
   |  addc ([], [], c) = [c]
   |  addc ((x::xs), [], c) =
    if (x + c) > emax then
      (x + c - (emax + 1))::(addc (xs, [], 1))
    else
      (x + c)::(addc (xs, [], 0))
   |  addc ([], (y::ys), c) =
    if (y + c - (emax + 1)) > emax then
      (y + c)::(addc ([], ys, 1))
    else
      (y + c)::(addc ([] ,ys, 0))
   |  addc ((x::xs), (y::ys), c) =
    if (x + y + c) > emax then
      (x + y + c - (emax + 1))::(addc (xs, ys, 1))
    else
      (x + y + c)::(addc (xs, ys, 0))

  fun add (x, y) = addc(x, y, 0)

end

