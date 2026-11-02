Theory vfmTest1092[no_sig_docs]
Ancestors vfmTestDefs1092
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1092_0.nsv", "result1092_1.nsv", "result1092_2.nsv", "result1092_3.nsv", "result1092_4.nsv", "result1092_5.nsv", "result1092_6.nsv", "result1092_7.nsv", "result1092_8.nsv", "result1092_9.nsv", "result1092_10.nsv", "result1092_11.nsv", "result1092_12.nsv", "result1092_13.nsv", "result1092_14.nsv", "result1092_15.nsv", "result1092_16.nsv", "result1092_17.nsv", "result1092_18.nsv", "result1092_19.nsv", "result1092_20.nsv", "result1092_21.nsv"];
val thyn = "vfmTestDefs1092";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
