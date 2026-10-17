Theory vfmTest1632[no_sig_docs]
Ancestors vfmTestDefs1632
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1632_0.nsv", "result1632_1.nsv", "result1632_2.nsv", "result1632_3.nsv", "result1632_4.nsv", "result1632_5.nsv", "result1632_6.nsv", "result1632_7.nsv", "result1632_8.nsv", "result1632_9.nsv", "result1632_10.nsv", "result1632_11.nsv"];
val thyn = "vfmTestDefs1632";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
