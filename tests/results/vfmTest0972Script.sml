Theory vfmTest0972[no_sig_docs]
Ancestors vfmTestDefs0972
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0972_0.nsv", "result0972_1.nsv", "result0972_2.nsv", "result0972_3.nsv", "result0972_4.nsv", "result0972_5.nsv", "result0972_6.nsv", "result0972_7.nsv", "result0972_8.nsv", "result0972_9.nsv", "result0972_10.nsv", "result0972_11.nsv"];
val thyn = "vfmTestDefs0972";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
