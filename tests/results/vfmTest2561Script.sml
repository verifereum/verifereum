Theory vfmTest2561[no_sig_docs]
Ancestors vfmTestDefs2561
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2561_0.nsv"];
val thyn = "vfmTestDefs2561";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
