Theory vfmTest0476[no_sig_docs]
Ancestors vfmTestDefs0476
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0476_0.nsv", "result0476_1.nsv", "result0476_2.nsv", "result0476_3.nsv", "result0476_4.nsv", "result0476_5.nsv", "result0476_6.nsv", "result0476_7.nsv", "result0476_8.nsv", "result0476_9.nsv"];
val thyn = "vfmTestDefs0476";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
