Theory vfmTest0391[no_sig_docs]
Ancestors vfmTestDefs0391
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0391";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
