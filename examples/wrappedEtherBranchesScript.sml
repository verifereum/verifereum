(* WETH's transfer(dst,wad) and transferFrom(src,dst,wad), each as one
   triple over every path from the function's entry, the reverting ones
   included: the block summaries of wrappedEtherTheory composed with
   compose_region, which merges the two sides of each JUMPI the path
   leaves open. *)
Theory wrappedEtherBranches
Ancestors
  arithmetic list words vfmExecution vfmBuffer set_sep prog vfmProg
  wrappedEther
Libs
  wordsLib cv_transLib evmDecompLib

fun weth_block n v =
  DB.fetch "wrappedEther" ("weth_block_" ^ Int.toString n ^ v)

val weth_summaries =
  map snd (List.filter (String.isPrefix "weth_block_" o fst)
                       (DB.thms "wrappedEther"))

val memory_cost_64_32 =
  Q.SPECL [`64`,`32`] (Q.GENL [`off`,`sz`] memory_cost_offset_to_0)
  |> SIMP_RULE arith_ss []

(* the selector's division by 2^224 is ground once the calldata is read *)
fun ground_div_conv tm =
  let val (f, _) = strip_comb tm in
    if is_const f andalso
       Lib.mem (fst (dest_const f)) ["with_zero", "word_div"] andalso
       null (free_vars tm)
    then
      let val th = EVAL tm in
        if rhs (concl th) ~~ tm then raise UNCHANGED else th
      end
    else raise UNCHANGED
  end
val () = augment_srw_ss [simpLib.named_merge_ss "ground_div" [simpLib.conv_ss
  {name = "ground_div", trace = 3, key = SOME ([], mk_var ("x", alpha)),
   conv = K (K ground_div_conv)}]]

(* wrappedEtherTransferScript's config *)
val branches_config : evmDecompLib.config =
  {code_eq = contract_code_eq, parsed_eq = parsed_contract_code_eq,
   hints = [],
   simps = [with_zero_def, mask_and_w2w, memory_cost_64_32,
            accesses_add_slot_accounts, buffer_take_write_same,
            buffer_take_write_after, buffer_take_write_before,
            buffer_take_expanded_memory, buffer_length_expanded_memory,
            word_to_bytes_bytes32_NIL,
            buffer_take_split |> Q.INST [`n1` |-> `32`, `n2` |-> `32`]
                              |> SIMP_RULE arith_ss [],
            MAX_LE, expanded_memory_leq, memory_cost_none_zero,
            memory_cost_buffer_write, memory_cost_add],
   strip_metadata = true}

fun var_named th n =
  valOf (List.find (fn v => fst (dest_var v) = n) (thm_frees th))

(* the dispatcher's path to a function's entry: the call starts with
   empty memory and no gas used *)
fun dispatch path =
  let
    val ths = map (fn (n, v) => weth_block n v) path
    val th0 = hd ths
    val th0 = INST [var_named th0 "m" |-> “empty_buffer”,
                    var_named th0 "g" |-> “0n”] th0
  in
    List.foldl (fn (th, acc) => compose_blocks branches_config [acc, th])
      th0 (tl ths)
  end

(* the region from the function's entry, checked to end in the expected
   paths (as entry pcs), all of them halting *)
fun region path expected =
  let
    val (th, paths) =
      compose_region branches_config weth_summaries (dispatch path)
    val _ = if paths = map (fn p => (p, "halt")) expected then ()
            else raise mk_HOL_ERR "wrappedEtherBranchesScript" "region"
                   "unexpected paths"
  in th end

(* ---------------------------------------------------------------- *)
(* transfer: the callvalue check at 880 (reverting at 887), the balance
   check at 1676 (reverting at 1752), and the transfer itself, returning
   at 944. The allowance branches at 1756 and 1972 are decided: the
   source is the caller. *)

Theorem weth_transfer_region =
  region
    [(0, "_skip"), (13, "_skip"), (65, "_skip"), (76, "_skip"),
     (87, "_skip"), (98, "_skip"), (109, "_skip"), (120, "_skip"),
     (131, "_skip"), (142, "_take")]
    [[880, 891, 3022, 1676, 1756, 1972, 2255, 3035, 944],
     [880, 891, 3022, 1676, 1752],
     [880, 887]]

(* ---------------------------------------------------------------- *)
(* transferFrom: besides the callvalue and balance checks, the allowance
   is read and checked when src is not the caller (1756) and the
   allowance is not the maximum (1972), reverting at 2112 when it is too
   small; all successful paths return at 553. *)

Theorem weth_transferFrom_region =
  region
    [(0, "_skip"), (13, "_skip"), (65, "_skip"), (76, "_skip"),
     (87, "_take")]
    [[458, 469, 1676, 1756, 1972, 2255, 553],
     [458, 469, 1676, 1756, 1811, 1972, 2255, 553],
     [458, 469, 1676, 1756, 1811, 1972, 1978, 2116, 2255, 553],
     [458, 469, 1676, 1756, 1811, 1972, 1978, 2112],
     [458, 469, 1676, 1752],
     [458, 465]]

val () = diminish_srw_ss ["ground_div"]
