Theory vfmTest2283[no_sig_docs]
Ancestors vfmTestDefs2283
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2283_0.nsv", "result2283_1.nsv"];
val thyn = "vfmTestDefs2283";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
