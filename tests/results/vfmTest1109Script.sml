Theory vfmTest1109[no_sig_docs]
Ancestors vfmTestDefs1109
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1109_0.nsv", "result1109_1.nsv", "result1109_2.nsv", "result1109_3.nsv", "result1109_4.nsv", "result1109_5.nsv", "result1109_6.nsv", "result1109_7.nsv", "result1109_8.nsv", "result1109_9.nsv", "result1109_10.nsv", "result1109_11.nsv", "result1109_12.nsv", "result1109_13.nsv", "result1109_14.nsv", "result1109_15.nsv"];
val thyn = "vfmTestDefs1109";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
