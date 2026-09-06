Theory vfmTest2274[no_sig_docs]
Ancestors vfmTestDefs2274
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2274_0.nsv", "result2274_1.nsv", "result2274_2.nsv", "result2274_3.nsv", "result2274_4.nsv", "result2274_5.nsv"];
val thyn = "vfmTestDefs2274";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
