Theory vfmTest1377[no_sig_docs]
Ancestors vfmTestDefs1377
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1377_0.nsv", "result1377_1.nsv", "result1377_2.nsv", "result1377_3.nsv", "result1377_4.nsv", "result1377_5.nsv", "result1377_6.nsv", "result1377_7.nsv"];
val thyn = "vfmTestDefs1377";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
