structure vfmTestAuxLib :> vfmTestAuxLib = struct
  open HolKernel

  (* Static annotations consumed by holbuild; no-ops when scripts run. *)
  fun holbuild_extra_deps (_ : string list) = ()
  fun holbuild_extra_outputs (_ : string list) = ()

  fun ss f = Substring.string o f o Substring.full
  fun trimr n = ss $ Substring.trimr n
  fun triml n = ss $ Substring.triml n
  val trim2 = triml 2

  val string_less = curry (equal LESS o String.compare)

  fun is_dir path = OS.FileSys.isDir path handle OS.SysErr _ => false
  fun is_file path =
    OS.FileSys.access(path, [OS.FileSys.A_READ]) handle OS.SysErr _ => false

  fun is_test_root path =
    is_file (OS.Path.concat(path, "vfmTestLib.sml")) andalso
    is_dir (OS.Path.concat(path, "defs")) andalso
    is_dir (OS.Path.concat(path, "results"))

  fun find_test_root () = let
    fun search path =
      if is_test_root path then SOME path
      else let val tests = OS.Path.concat(path, "tests") in
        if is_test_root tests then SOME tests
        else let val parent = OS.Path.dir path in
          if parent = path then NONE else search parent
        end
      end
  in
    search (OS.Path.mkCanonical $ OS.FileSys.getDir ())
  end

  fun test_root () =
    case find_test_root () of
      SOME path => path
    | NONE => raise Fail
        "could not locate the Verifereum tests directory from the current directory"

  fun test_path path = OS.Path.concat(test_root (), path)
  fun fixtures_path path = OS.Path.concat(test_path "fixtures", path)
  fun defs_path path = OS.Path.concat(test_path "defs", path)
  fun results_path path = OS.Path.concat(test_path "results", path)

  fun padl n z s = let
    val m = String.size s
  in
    if m < n
    then (String.implode (List.tabulate(n-m, K z))) ^ s
    else s
  end

  val fixtures_version = "5.4.0"
  val fork_name = "Osaka"
  val chain_id = 1

  val time_limit = Option.getOpt
    (Option.mapPartial Time.fromString
      (OS.Process.getEnv "VFM_TIME_LIMIT"),
     Time.fromSeconds 60)
end
