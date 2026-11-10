Theory vfmTest2815[no_sig_docs]
Ancestors vfmTestDefs2815
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2815_0.nsv", "result2815_1.nsv", "result2815_2.nsv", "result2815_3.nsv", "result2815_4.nsv", "result2815_5.nsv", "result2815_6.nsv", "result2815_7.nsv", "result2815_8.nsv", "result2815_9.nsv", "result2815_10.nsv", "result2815_11.nsv", "result2815_12.nsv", "result2815_13.nsv", "result2815_14.nsv", "result2815_15.nsv", "result2815_16.nsv", "result2815_17.nsv"];
val thyn = "vfmTestDefs2815";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
