Theory vfmTest0704[no_sig_docs]
Ancestors vfmTestDefs0704
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0704_0.nsv", "result0704_1.nsv", "result0704_2.nsv", "result0704_3.nsv", "result0704_4.nsv", "result0704_5.nsv", "result0704_6.nsv", "result0704_7.nsv", "result0704_8.nsv", "result0704_9.nsv", "result0704_10.nsv", "result0704_11.nsv", "result0704_12.nsv", "result0704_13.nsv", "result0704_14.nsv", "result0704_15.nsv"];
val thyn = "vfmTestDefs0704";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
