structure contractABISyntax :> contractABISyntax = struct
  open HolKernel boolLib contractABITheory

  val abi_type_ty = mk_thy_type{Args=[],Thy="contractABI",Tyop="abi_type"}
  fun pmc s = prim_mk_const{Thy="contractABI",Name=s}
  val Bool_tm = pmc"Bool"
  val String_tm = pmc"String"
  val Bytes_tm = pmc"Bytes"
  val Uint_tm = pmc"Uint"
  val Int_tm = pmc"Int"
  val Array_tm = pmc"Array"
  val Tuple_tm = pmc"Tuple"
  val Address_tm = pmc"Address"

  fun skip_to_matching_paren ss = let
    fun skip_to_close i = let
      val c = Substring.sub(ss, i)
      val i = i+1
    in
      if c = #"]" then i else skip_to_close i
    end
    fun loop n i = let
      val c = Substring.sub(ss, i)
      val i = i+1
    in
      if c = #"(" then loop (n+1) i else
      if c = #")" then
        if n = 1
        then if i < Substring.size ss andalso
                Substring.sub(ss, i) = #"["
             then skip_to_close (i+1)
             else i
        else loop (n-1) i
      else loop n i
    end
  in
    Substring.splitAt(ss, loop 0 0)
  end

  fun split_on_outer_commas ss = let
    val (x,ss) =
      (if Substring.sub(ss, 0) = #"("
       then skip_to_matching_paren
       else Substring.splitl (not o equal #",")) ss
  in
    if Substring.size ss = 0 then [x]
    else x :: split_on_outer_commas (Substring.triml 1 ss)
  end

  fun parse_optnum_ss ns =
    case Int.fromString $ Substring.string ns
      of SOME n => optionSyntax.mk_some (numSyntax.term_of_int n)
       | NONE => optionSyntax.mk_none numSyntax.num

  fun parse_abi_type_ss ss =
    if Substring.isSuffix "]" ss then let
      val (ps, ns) = Substring.splitr (not o equal #"[") ss
      val bt = parse_optnum_ss ns
      val ss = Substring.trimr 1 ps
      val t = parse_abi_type_ss ss
    in list_mk_comb(Array_tm, [bt, t]) end
    else if Substring.isPrefix "(" ss then let
      val ss = Substring.trimr 1 $ Substring.triml 1 $ ss
      val tss = split_on_outer_commas ss
      val ts = List.map parse_abi_type_ss tss
      val ls = listSyntax.mk_list(ts, abi_type_ty)
    in mk_comb(Tuple_tm, ls) end
    else if Substring.isPrefix "uint" ss then let
      val ns = Substring.triml 4 ss
      val SOME n = Int.fromString (Substring.string ns)
      val nt = numSyntax.term_of_int n
    in mk_comb(Uint_tm, nt) end
    else if Substring.isPrefix "int" ss then let
      val ns = Substring.triml 3 ss
      val SOME n = Int.fromString (Substring.string ns)
      val nt = numSyntax.term_of_int n
    in mk_comb(Int_tm, nt) end
    else if Substring.isPrefix "bytes" ss then let
      val ns = Substring.triml 5 ss
      val bt = parse_optnum_ss ns
    in mk_comb(Bytes_tm, bt) end
    (* TODO: Fixed, Ufixed *)
    else let val s = Substring.string ss
    in   if s = "bool" then Bool_tm
    else if s = "address" then Address_tm
    else if s = "string" then String_tm
    else raise Fail ("parse_abi_type_ss: " ^ s) end

  val parse_abi_type = parse_abi_type_ss o Substring.full

end
