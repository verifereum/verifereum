signature vfmTestResultLib = sig

  val get_result_defs : string -> (string * Thm.thm) list
  val save_result_thm : string -> (string * Thm.thm) -> Thm.thm

end
