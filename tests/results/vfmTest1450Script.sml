Theory vfmTest1450[no_sig_docs]
Ancestors vfmTestDefs1450
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1450_0.nsv", "result1450_1.nsv", "result1450_2.nsv", "result1450_3.nsv", "result1450_4.nsv", "result1450_5.nsv", "result1450_6.nsv", "result1450_7.nsv", "result1450_8.nsv", "result1450_9.nsv", "result1450_10.nsv", "result1450_11.nsv"];
val thyn = "vfmTestDefs1450";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
