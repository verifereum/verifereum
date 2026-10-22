signature vfmUncheckedFixtureLib = sig
  (* Parsing is shared with the certified loader.  Each evaluate closure
     performs all native fixture encoding and execution, so both are covered by
     its timeout.  gas is the sum of the blocks' header gasUsed, each capped at
     its block's gasLimit; it sizes the case's time limit. *)
  val json_path_to_tests : string ->
    {name: string, gas: Arbnum.num, evaluate: unit -> string} list
end
