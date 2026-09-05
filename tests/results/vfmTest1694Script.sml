Theory vfmTest1694[no_sig_docs]
Ancestors vfmTestDefs1694
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1694_0.nsv", "result1694_1.nsv", "result1694_2.nsv", "result1694_3.nsv", "result1694_4.nsv", "result1694_5.nsv", "result1694_6.nsv", "result1694_7.nsv", "result1694_8.nsv", "result1694_9.nsv", "result1694_10.nsv", "result1694_11.nsv", "result1694_12.nsv", "result1694_13.nsv", "result1694_14.nsv", "result1694_15.nsv", "result1694_16.nsv", "result1694_17.nsv", "result1694_18.nsv", "result1694_19.nsv"];
val thyn = "vfmTestDefs1694";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
