Theory vfmTest1108[no_sig_docs]
Ancestors vfmTestDefs1108
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1108_0.nsv", "result1108_1.nsv", "result1108_2.nsv", "result1108_3.nsv", "result1108_4.nsv", "result1108_5.nsv", "result1108_6.nsv", "result1108_7.nsv", "result1108_8.nsv", "result1108_9.nsv", "result1108_10.nsv", "result1108_11.nsv", "result1108_12.nsv", "result1108_13.nsv", "result1108_14.nsv", "result1108_15.nsv", "result1108_16.nsv", "result1108_17.nsv", "result1108_18.nsv", "result1108_19.nsv", "result1108_20.nsv", "result1108_21.nsv"];
val thyn = "vfmTestDefs1108";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
