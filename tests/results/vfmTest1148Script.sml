Theory vfmTest1148[no_sig_docs]
Ancestors vfmTestDefs1148
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1148_0.nsv"];
val thyn = "vfmTestDefs1148";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
