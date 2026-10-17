Theory vfmTest1658[no_sig_docs]
Ancestors vfmTestDefs1658
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1658_0.nsv", "result1658_1.nsv", "result1658_2.nsv", "result1658_3.nsv", "result1658_4.nsv", "result1658_5.nsv", "result1658_6.nsv", "result1658_7.nsv", "result1658_8.nsv", "result1658_9.nsv", "result1658_10.nsv", "result1658_11.nsv", "result1658_12.nsv", "result1658_13.nsv", "result1658_14.nsv", "result1658_15.nsv", "result1658_16.nsv", "result1658_17.nsv", "result1658_18.nsv", "result1658_19.nsv"];
val thyn = "vfmTestDefs1658";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
