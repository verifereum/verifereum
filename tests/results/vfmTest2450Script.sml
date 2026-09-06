Theory vfmTest2450[no_sig_docs]
Ancestors vfmTestDefs2450
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2450_0.nsv", "result2450_1.nsv"];
val thyn = "vfmTestDefs2450";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
