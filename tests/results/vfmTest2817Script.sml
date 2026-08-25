Theory vfmTest2817[no_sig_docs]
Ancestors vfmTestDefs2817
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2817_0.nsv", "result2817_1.nsv", "result2817_2.nsv", "result2817_3.nsv"];
val thyn = "vfmTestDefs2817";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
