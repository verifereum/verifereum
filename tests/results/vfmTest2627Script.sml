Theory vfmTest2627[no_sig_docs]
Ancestors vfmTestDefs2627
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2627_0.nsv", "result2627_1.nsv", "result2627_2.nsv", "result2627_3.nsv"];
val thyn = "vfmTestDefs2627";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
