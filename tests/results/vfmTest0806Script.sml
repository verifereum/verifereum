Theory vfmTest0806[no_sig_docs]
Ancestors vfmTestDefs0806
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0806_0.nsv", "result0806_1.nsv", "result0806_2.nsv", "result0806_3.nsv", "result0806_4.nsv", "result0806_5.nsv", "result0806_6.nsv", "result0806_7.nsv"];
val thyn = "vfmTestDefs0806";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
