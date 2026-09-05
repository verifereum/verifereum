Theory vfmTest2378[no_sig_docs]
Ancestors vfmTestDefs2378
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2378_0.nsv", "result2378_1.nsv"];
val thyn = "vfmTestDefs2378";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
