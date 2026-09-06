Theory vfmTest1691[no_sig_docs]
Ancestors vfmTestDefs1691
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1691_0.nsv", "result1691_1.nsv", "result1691_2.nsv", "result1691_3.nsv", "result1691_4.nsv", "result1691_5.nsv", "result1691_6.nsv", "result1691_7.nsv", "result1691_8.nsv", "result1691_9.nsv", "result1691_10.nsv", "result1691_11.nsv", "result1691_12.nsv", "result1691_13.nsv", "result1691_14.nsv", "result1691_15.nsv", "result1691_16.nsv", "result1691_17.nsv", "result1691_18.nsv", "result1691_19.nsv"];
val thyn = "vfmTestDefs1691";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
