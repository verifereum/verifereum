Theory vfmTest2461[no_sig_docs]
Ancestors vfmTestDefs2461
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2461_0.nsv"];
val thyn = "vfmTestDefs2461";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
