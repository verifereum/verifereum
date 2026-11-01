Theory vfmTest0627[no_sig_docs]
Ancestors vfmTestDefs0627
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0627_0.nsv", "result0627_1.nsv", "result0627_2.nsv", "result0627_3.nsv", "result0627_4.nsv", "result0627_5.nsv", "result0627_6.nsv", "result0627_7.nsv", "result0627_8.nsv", "result0627_9.nsv"];
val thyn = "vfmTestDefs0627";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
