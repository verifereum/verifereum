Theory vfmTest1755[no_sig_docs]
Ancestors vfmTestDefs1755
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1755";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
