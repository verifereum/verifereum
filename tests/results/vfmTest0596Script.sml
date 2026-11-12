Theory vfmTest0596[no_sig_docs]
Ancestors vfmTestDefs0596
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0596_0.nsv", "result0596_1.nsv", "result0596_2.nsv", "result0596_3.nsv", "result0596_4.nsv", "result0596_5.nsv", "result0596_6.nsv", "result0596_7.nsv", "result0596_8.nsv", "result0596_9.nsv", "result0596_10.nsv", "result0596_11.nsv"];
val thyn = "vfmTestDefs0596";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
