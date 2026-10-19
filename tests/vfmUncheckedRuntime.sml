(* Native operations for the CV datatype.  These are the total operations of
   cvTheory, not operations on a decoded HOL term or an evaluator instruction. *)
structure vfmUncheckedRuntime = struct
  datatype cv = Num of Arbnum.num | Pair of cv * cv

  (* EmitML's numeral spelling, with the same representation as the fixture
     encoder.  This deliberately does not use emit's unary/binary numML type. *)
  structure numML = struct
    val ZERO = Arbnum.zero
    val ONE = Arbnum.one
    val TWO = Arbnum.two
    val fromString = Arbnum.fromString
  end

  val zero = Num Arbnum.zero
  val one = Num Arbnum.one
  fun number (Num n) = n | number (Pair _) = Arbnum.zero
  fun c2b (Num n) = n <> Arbnum.zero | c2b (Pair _) = false
  fun cv_fst (Pair (x, _)) = x | cv_fst (Num _) = zero
  fun cv_snd (Pair (_, y)) = y | cv_snd (Num _) = zero
  fun cv_ispair (Pair _) = one | cv_ispair (Num _) = zero
  fun cv_add x y = Num (Arbnum.+ (number x, number y))
  fun cv_sub x y =
    let val a = number x and b = number y in
      if Arbnum.< (a, b) then zero else Num (Arbnum.- (a, b))
    end
  fun cv_mul x y = Num (Arbnum.* (number x, number y))
  fun cv_div x y =
    let val b = number y in
      if b = Arbnum.zero then zero else Num (Arbnum.div (number x, b))
    end
  fun cv_mod x y =
    let val a = number x and b = number y in
      Num (if b = Arbnum.zero then a else Arbnum.mod (a, b))
    end
  fun cv_lt (Num a) (Num b) = if Arbnum.< (a, b) then one else zero
    | cv_lt _ _ = zero
  fun cv_eq x y = if x = y then one else zero

  fun string_of_cv value =
    let
      fun chars (Num n) acc =
            if n = Arbnum.zero then String.implode (List.rev acc)
            else raise Fail "invalid CV string terminator"
        | chars (Pair (Num n, rest)) acc =
            chars rest (Char.chr (Arbnum.toInt n) :: acc)
        | chars _ _ = raise Fail "invalid CV character"
    in chars value [] end

  fun hex_of_cv (Num n) = "0x" ^ Arbnum.toHexString n
    | hex_of_cv _ = raise Fail "invalid CV result word"
end
