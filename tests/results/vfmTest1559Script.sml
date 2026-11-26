Theory vfmTest1559[no_sig_docs]
Ancestors vfmTestDefs1559
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1559_0.nsv", "result1559_1.nsv", "result1559_2.nsv", "result1559_3.nsv", "result1559_4.nsv", "result1559_5.nsv", "result1559_6.nsv", "result1559_7.nsv", "result1559_8.nsv", "result1559_9.nsv", "result1559_10.nsv", "result1559_11.nsv", "result1559_12.nsv", "result1559_13.nsv", "result1559_14.nsv", "result1559_15.nsv", "result1559_16.nsv", "result1559_17.nsv", "result1559_18.nsv", "result1559_19.nsv"];
val thyn = "vfmTestDefs1559";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
