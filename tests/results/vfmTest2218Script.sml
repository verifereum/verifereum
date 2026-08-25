Theory vfmTest2218[no_sig_docs]
Ancestors vfmTestDefs2218
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2218_0.nsv"];
val thyn = "vfmTestDefs2218";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
