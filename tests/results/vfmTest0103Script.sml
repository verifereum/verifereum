Theory vfmTest0103[no_sig_docs]
Ancestors vfmTestDefs0103
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0103_0.nsv", "result0103_1.nsv", "result0103_2.nsv", "result0103_3.nsv", "result0103_4.nsv", "result0103_5.nsv", "result0103_6.nsv", "result0103_7.nsv", "result0103_8.nsv", "result0103_9.nsv", "result0103_10.nsv", "result0103_11.nsv"];
val thyn = "vfmTestDefs0103";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
