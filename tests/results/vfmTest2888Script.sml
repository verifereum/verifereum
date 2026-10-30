Theory vfmTest2888[no_sig_docs]
Ancestors vfmTestDefs2888
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2888_0.nsv"];
val thyn = "vfmTestDefs2888";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
