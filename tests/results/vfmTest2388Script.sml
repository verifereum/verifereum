Theory vfmTest2388[no_sig_docs]
Ancestors vfmTestDefs2388
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2388_0.nsv", "result2388_1.nsv", "result2388_2.nsv", "result2388_3.nsv", "result2388_4.nsv", "result2388_5.nsv", "result2388_6.nsv", "result2388_7.nsv", "result2388_8.nsv", "result2388_9.nsv", "result2388_10.nsv", "result2388_11.nsv", "result2388_12.nsv", "result2388_13.nsv", "result2388_14.nsv", "result2388_15.nsv", "result2388_16.nsv", "result2388_17.nsv", "result2388_18.nsv", "result2388_19.nsv"];
val thyn = "vfmTestDefs2388";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
