Theory vfmTest2291[no_sig_docs]
Ancestors vfmTestDefs2291
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2291_0.nsv", "result2291_1.nsv", "result2291_2.nsv", "result2291_3.nsv", "result2291_4.nsv", "result2291_5.nsv", "result2291_6.nsv", "result2291_7.nsv", "result2291_8.nsv", "result2291_9.nsv", "result2291_10.nsv", "result2291_11.nsv", "result2291_12.nsv", "result2291_13.nsv", "result2291_14.nsv", "result2291_15.nsv", "result2291_16.nsv", "result2291_17.nsv", "result2291_18.nsv", "result2291_19.nsv", "result2291_20.nsv", "result2291_21.nsv", "result2291_22.nsv", "result2291_23.nsv", "result2291_24.nsv", "result2291_25.nsv", "result2291_26.nsv"];
val thyn = "vfmTestDefs2291";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
