Theory vfmTest1509[no_sig_docs]
Ancestors vfmTestDefs1509
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs1509";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
