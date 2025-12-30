Theory vfmTest1658[no_sig_docs]
Ancestors vfmTestDefs1658
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1658";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
