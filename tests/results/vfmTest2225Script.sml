Theory vfmTest2225[no_sig_docs]
Ancestors vfmTestDefs2225
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2225_0.nsv", "result2225_1.nsv", "result2225_2.nsv", "result2225_3.nsv", "result2225_4.nsv", "result2225_5.nsv", "result2225_6.nsv", "result2225_7.nsv", "result2225_8.nsv", "result2225_9.nsv", "result2225_10.nsv", "result2225_11.nsv", "result2225_12.nsv", "result2225_13.nsv", "result2225_14.nsv", "result2225_15.nsv", "result2225_16.nsv", "result2225_17.nsv", "result2225_18.nsv"];
val thyn = "vfmTestDefs2225";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
