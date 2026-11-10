Theory vfmTest2872[no_sig_docs]
Ancestors vfmTestDefs2872
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2872_0.nsv"];
val thyn = "vfmTestDefs2872";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
