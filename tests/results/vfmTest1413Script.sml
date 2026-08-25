Theory vfmTest1413[no_sig_docs]
Ancestors vfmTestDefs1413
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1413_0.nsv"];
val thyn = "vfmTestDefs1413";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
