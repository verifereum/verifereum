Theory vfmTest1442[no_sig_docs]
Ancestors vfmTestDefs1442
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1442_0.nsv", "result1442_1.nsv", "result1442_2.nsv", "result1442_3.nsv", "result1442_4.nsv", "result1442_5.nsv", "result1442_6.nsv", "result1442_7.nsv", "result1442_8.nsv", "result1442_9.nsv", "result1442_10.nsv", "result1442_11.nsv", "result1442_12.nsv", "result1442_13.nsv", "result1442_14.nsv", "result1442_15.nsv", "result1442_16.nsv", "result1442_17.nsv", "result1442_18.nsv", "result1442_19.nsv", "result1442_20.nsv", "result1442_21.nsv", "result1442_22.nsv", "result1442_23.nsv"];
val thyn = "vfmTestDefs1442";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
