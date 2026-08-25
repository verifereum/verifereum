Theory vfmTest2285[no_sig_docs]
Ancestors vfmTestDefs2285
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2285_0.nsv", "result2285_1.nsv", "result2285_2.nsv"];
val thyn = "vfmTestDefs2285";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
