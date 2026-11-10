Theory vfmTest0497[no_sig_docs]
Ancestors vfmTestDefs0497
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0497_0.nsv", "result0497_1.nsv", "result0497_2.nsv", "result0497_3.nsv", "result0497_4.nsv", "result0497_5.nsv", "result0497_6.nsv", "result0497_7.nsv", "result0497_8.nsv", "result0497_9.nsv"];
val thyn = "vfmTestDefs0497";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
