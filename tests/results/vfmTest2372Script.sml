Theory vfmTest2372[no_sig_docs]
Ancestors vfmTestDefs2372
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2372_0.nsv"];
val thyn = "vfmTestDefs2372";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
