Theory vfmTest1557[no_sig_docs]
Ancestors vfmTestDefs1557
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1557_0.nsv", "result1557_1.nsv", "result1557_2.nsv", "result1557_3.nsv", "result1557_4.nsv", "result1557_5.nsv", "result1557_6.nsv", "result1557_7.nsv", "result1557_8.nsv", "result1557_9.nsv", "result1557_10.nsv", "result1557_11.nsv", "result1557_12.nsv", "result1557_13.nsv", "result1557_14.nsv", "result1557_15.nsv", "result1557_16.nsv", "result1557_17.nsv", "result1557_18.nsv", "result1557_19.nsv"];
val thyn = "vfmTestDefs1557";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
