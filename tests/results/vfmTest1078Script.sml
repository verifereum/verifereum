Theory vfmTest1078[no_sig_docs]
Ancestors vfmTestDefs1078
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1078_0.nsv", "result1078_1.nsv", "result1078_2.nsv", "result1078_3.nsv", "result1078_4.nsv", "result1078_5.nsv", "result1078_6.nsv", "result1078_7.nsv", "result1078_8.nsv", "result1078_9.nsv", "result1078_10.nsv", "result1078_11.nsv", "result1078_12.nsv", "result1078_13.nsv", "result1078_14.nsv", "result1078_15.nsv"];
val thyn = "vfmTestDefs1078";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
