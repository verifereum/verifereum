Theory vfmTest1113[no_sig_docs]
Ancestors vfmTestDefs1113
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1113_0.nsv", "result1113_1.nsv"];
val thyn = "vfmTestDefs1113";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
