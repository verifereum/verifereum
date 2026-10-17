Theory vfmTest2353[no_sig_docs]
Ancestors vfmTestDefs2353
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2353_0.nsv"];
val thyn = "vfmTestDefs2353";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
