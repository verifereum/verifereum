Theory vfmTest2728[no_sig_docs]
Ancestors vfmTestDefs2728
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2728_0.nsv", "result2728_1.nsv", "result2728_2.nsv", "result2728_3.nsv"];
val thyn = "vfmTestDefs2728";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
