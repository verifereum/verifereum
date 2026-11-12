Theory vfmTest1554[no_sig_docs]
Ancestors vfmTestDefs1554
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1554_0.nsv", "result1554_1.nsv", "result1554_2.nsv", "result1554_3.nsv", "result1554_4.nsv", "result1554_5.nsv", "result1554_6.nsv", "result1554_7.nsv", "result1554_8.nsv", "result1554_9.nsv", "result1554_10.nsv", "result1554_11.nsv", "result1554_12.nsv", "result1554_13.nsv", "result1554_14.nsv", "result1554_15.nsv", "result1554_16.nsv", "result1554_17.nsv", "result1554_18.nsv", "result1554_19.nsv"];
val thyn = "vfmTestDefs1554";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
