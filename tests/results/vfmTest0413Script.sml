Theory vfmTest0413[no_sig_docs]
Ancestors vfmTestDefs0413
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0413_0.nsv", "result0413_1.nsv", "result0413_2.nsv", "result0413_3.nsv", "result0413_4.nsv", "result0413_5.nsv", "result0413_6.nsv", "result0413_7.nsv", "result0413_8.nsv", "result0413_9.nsv", "result0413_10.nsv", "result0413_11.nsv", "result0413_12.nsv", "result0413_13.nsv", "result0413_14.nsv", "result0413_15.nsv", "result0413_16.nsv", "result0413_17.nsv", "result0413_18.nsv", "result0413_19.nsv"];
val thyn = "vfmTestDefs0413";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
