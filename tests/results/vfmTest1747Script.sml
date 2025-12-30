Theory vfmTest1747[no_sig_docs]
Ancestors vfmTestDefs1747
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1747";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
