Theory vfmTest1793[no_sig_docs]
Ancestors vfmTestDefs1793
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1793";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
