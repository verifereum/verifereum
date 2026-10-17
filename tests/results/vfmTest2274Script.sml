Theory vfmTest2274[no_sig_docs]
Ancestors vfmTestDefs2274
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2274_0.nsv", "result2274_1.nsv", "result2274_2.nsv", "result2274_3.nsv", "result2274_4.nsv", "result2274_5.nsv", "result2274_6.nsv", "result2274_7.nsv", "result2274_8.nsv", "result2274_9.nsv", "result2274_10.nsv", "result2274_11.nsv", "result2274_12.nsv", "result2274_13.nsv", "result2274_14.nsv", "result2274_15.nsv", "result2274_16.nsv", "result2274_17.nsv", "result2274_18.nsv"];
val thyn = "vfmTestDefs2274";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
