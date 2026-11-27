Theory vfmTest2138[no_sig_docs]
Ancestors vfmTestDefs2138
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2138_0.nsv", "result2138_1.nsv", "result2138_2.nsv", "result2138_3.nsv", "result2138_4.nsv", "result2138_5.nsv"];
val thyn = "vfmTestDefs2138";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
