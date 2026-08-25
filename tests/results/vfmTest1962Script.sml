Theory vfmTest1962[no_sig_docs]
Ancestors vfmTestDefs1962
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1962_0.nsv", "result1962_1.nsv", "result1962_2.nsv", "result1962_3.nsv"];
val thyn = "vfmTestDefs1962";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
