Theory vfmTest2506[no_sig_docs]
Ancestors vfmTestDefs2506
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2506_0.nsv"];
val thyn = "vfmTestDefs2506";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
