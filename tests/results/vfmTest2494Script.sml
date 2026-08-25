Theory vfmTest2494[no_sig_docs]
Ancestors vfmTestDefs2494
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2494_0.nsv"];
val thyn = "vfmTestDefs2494";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
