Theory vfmTest0848[no_sig_docs]
Ancestors vfmTestDefs0848
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0848_0.nsv", "result0848_1.nsv", "result0848_2.nsv", "result0848_3.nsv", "result0848_4.nsv", "result0848_5.nsv", "result0848_6.nsv", "result0848_7.nsv", "result0848_8.nsv", "result0848_9.nsv"];
val thyn = "vfmTestDefs0848";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
