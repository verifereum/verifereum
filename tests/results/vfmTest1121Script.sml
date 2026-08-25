Theory vfmTest1121[no_sig_docs]
Ancestors vfmTestDefs1121
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1121_0.nsv", "result1121_1.nsv"];
val thyn = "vfmTestDefs1121";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
