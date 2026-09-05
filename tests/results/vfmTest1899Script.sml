Theory vfmTest1899[no_sig_docs]
Ancestors vfmTestDefs1899
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1899_0.nsv", "result1899_1.nsv"];
val thyn = "vfmTestDefs1899";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
