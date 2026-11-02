Theory vfmTest2852[no_sig_docs]
Ancestors vfmTestDefs2852
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2852_0.nsv"];
val thyn = "vfmTestDefs2852";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
