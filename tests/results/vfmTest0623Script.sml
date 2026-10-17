Theory vfmTest0623[no_sig_docs]
Ancestors vfmTestDefs0623
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0623_0.nsv", "result0623_1.nsv", "result0623_2.nsv", "result0623_3.nsv", "result0623_4.nsv", "result0623_5.nsv", "result0623_6.nsv", "result0623_7.nsv", "result0623_8.nsv", "result0623_9.nsv", "result0623_10.nsv", "result0623_11.nsv"];
val thyn = "vfmTestDefs0623";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
