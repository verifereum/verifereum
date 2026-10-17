Theory vfmTest0728[no_sig_docs]
Ancestors vfmTestDefs0728
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0728_0.nsv", "result0728_1.nsv", "result0728_2.nsv", "result0728_3.nsv", "result0728_4.nsv", "result0728_5.nsv", "result0728_6.nsv", "result0728_7.nsv", "result0728_8.nsv", "result0728_9.nsv"];
val thyn = "vfmTestDefs0728";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
