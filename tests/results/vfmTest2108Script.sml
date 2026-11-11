Theory vfmTest2108[no_sig_docs]
Ancestors vfmTestDefs2108
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2108_0.nsv", "result2108_1.nsv", "result2108_2.nsv", "result2108_3.nsv", "result2108_4.nsv", "result2108_5.nsv", "result2108_6.nsv", "result2108_7.nsv", "result2108_8.nsv", "result2108_9.nsv", "result2108_10.nsv"];
val thyn = "vfmTestDefs2108";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
