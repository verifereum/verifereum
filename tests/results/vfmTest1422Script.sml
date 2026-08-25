Theory vfmTest1422[no_sig_docs]
Ancestors vfmTestDefs1422
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1422_0.nsv"];
val thyn = "vfmTestDefs1422";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
