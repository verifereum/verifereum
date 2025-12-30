Theory vfmTest0469[no_sig_docs]
Ancestors vfmTestDefs0469
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0469";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
