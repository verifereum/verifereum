Theory vfmTest1310[no_sig_docs]
Ancestors vfmTestDefs1310
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1310_0.nsv"];
val thyn = "vfmTestDefs1310";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
