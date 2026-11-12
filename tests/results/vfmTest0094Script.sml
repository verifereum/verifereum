Theory vfmTest0094[no_sig_docs]
Ancestors vfmTestDefs0094
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0094_0.nsv", "result0094_1.nsv", "result0094_2.nsv", "result0094_3.nsv", "result0094_4.nsv", "result0094_5.nsv"];
val thyn = "vfmTestDefs0094";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
