Theory vfmTest1563[no_sig_docs]
Ancestors vfmTestDefs1563
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1563_0.nsv", "result1563_1.nsv", "result1563_2.nsv", "result1563_3.nsv", "result1563_4.nsv", "result1563_5.nsv", "result1563_6.nsv", "result1563_7.nsv", "result1563_8.nsv", "result1563_9.nsv", "result1563_10.nsv", "result1563_11.nsv", "result1563_12.nsv", "result1563_13.nsv", "result1563_14.nsv", "result1563_15.nsv", "result1563_16.nsv", "result1563_17.nsv", "result1563_18.nsv", "result1563_19.nsv"];
val thyn = "vfmTestDefs1563";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
