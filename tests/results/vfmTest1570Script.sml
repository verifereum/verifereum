Theory vfmTest1570[no_sig_docs]
Ancestors vfmTestDefs1570
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1570_0.nsv", "result1570_1.nsv", "result1570_2.nsv", "result1570_3.nsv", "result1570_4.nsv", "result1570_5.nsv", "result1570_6.nsv", "result1570_7.nsv", "result1570_8.nsv", "result1570_9.nsv", "result1570_10.nsv", "result1570_11.nsv", "result1570_12.nsv", "result1570_13.nsv", "result1570_14.nsv", "result1570_15.nsv", "result1570_16.nsv", "result1570_17.nsv", "result1570_18.nsv", "result1570_19.nsv"];
val thyn = "vfmTestDefs1570";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
