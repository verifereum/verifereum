Theory vfmTest0296[no_sig_docs]
Ancestors vfmTestDefs0296
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0296_0.nsv", "result0296_1.nsv", "result0296_2.nsv", "result0296_3.nsv", "result0296_4.nsv", "result0296_5.nsv", "result0296_6.nsv", "result0296_7.nsv", "result0296_8.nsv", "result0296_9.nsv", "result0296_10.nsv", "result0296_11.nsv", "result0296_12.nsv", "result0296_13.nsv", "result0296_14.nsv", "result0296_15.nsv", "result0296_16.nsv", "result0296_17.nsv", "result0296_18.nsv"];
val thyn = "vfmTestDefs0296";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
