Theory vfmTest1985[no_sig_docs]
Ancestors vfmTestDefs1985
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1985_0.nsv", "result1985_1.nsv", "result1985_2.nsv", "result1985_3.nsv", "result1985_4.nsv", "result1985_5.nsv", "result1985_6.nsv", "result1985_7.nsv", "result1985_8.nsv", "result1985_9.nsv", "result1985_10.nsv", "result1985_11.nsv", "result1985_12.nsv", "result1985_13.nsv", "result1985_14.nsv", "result1985_15.nsv", "result1985_16.nsv", "result1985_17.nsv", "result1985_18.nsv", "result1985_19.nsv"];
val thyn = "vfmTestDefs1985";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
