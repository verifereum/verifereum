structure vfmTestAuxLib :> vfmTestAuxLib = struct
  open HolKernel

  fun ss f = Substring.string o f o Substring.full
  fun trimr n = ss $ Substring.trimr n
  fun triml n = ss $ Substring.triml n
  val trim2 = triml 2

  val string_less = curry (equal LESS o String.compare)

  fun padl n z s = let
    val m = String.size s
  in
    if m < n
    then (String.implode (List.tabulate(n-m, K z))) ^ s
    else s
  end

  val export_theory_no_docs = fn () =>
    Feedback.set_trace "TheoryPP.include_docs" 0
    before export_theory ()

  val fixtures_version = "5.4.0"
  val fork_name = "Cancun"
  val chain_id = 1

  val time_limit = Option.getOpt
    (Option.mapPartial Time.fromString
      (OS.Process.getEnv "VFM_TIME_LIMIT"),
     Time.fromSeconds 60)
end
