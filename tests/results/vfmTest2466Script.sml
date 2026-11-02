Theory vfmTest2466[no_sig_docs]
Ancestors vfmTestDefs2466
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2466_0.nsv"];
val thyn = "vfmTestDefs2466";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
