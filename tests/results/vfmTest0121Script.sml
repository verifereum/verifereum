Theory vfmTest0121[no_sig_docs]
Ancestors vfmTestDefs0121
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0121_0.nsv", "result0121_1.nsv", "result0121_2.nsv", "result0121_3.nsv", "result0121_4.nsv", "result0121_5.nsv", "result0121_6.nsv", "result0121_7.nsv", "result0121_8.nsv", "result0121_9.nsv", "result0121_10.nsv", "result0121_11.nsv", "result0121_12.nsv", "result0121_13.nsv", "result0121_14.nsv", "result0121_15.nsv", "result0121_16.nsv", "result0121_17.nsv"];
val thyn = "vfmTestDefs0121";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
