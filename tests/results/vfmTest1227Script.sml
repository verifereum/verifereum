Theory vfmTest1227[no_sig_docs]
Ancestors vfmTestDefs1227
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1227_0.nsv", "result1227_1.nsv", "result1227_2.nsv", "result1227_3.nsv"];
val thyn = "vfmTestDefs1227";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
