Theory vfmTest2491[no_sig_docs]
Ancestors vfmTestDefs2491
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2491_0.nsv", "result2491_1.nsv"];
val thyn = "vfmTestDefs2491";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
