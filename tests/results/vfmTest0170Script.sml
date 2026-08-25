Theory vfmTest0170[no_sig_docs]
Ancestors vfmTestDefs0170
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0170_0.nsv", "result0170_1.nsv", "result0170_2.nsv", "result0170_3.nsv", "result0170_4.nsv", "result0170_5.nsv", "result0170_6.nsv", "result0170_7.nsv", "result0170_8.nsv", "result0170_9.nsv", "result0170_10.nsv", "result0170_11.nsv", "result0170_12.nsv", "result0170_13.nsv", "result0170_14.nsv", "result0170_15.nsv", "result0170_16.nsv", "result0170_17.nsv", "result0170_18.nsv", "result0170_19.nsv", "result0170_20.nsv"];
val thyn = "vfmTestDefs0170";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
