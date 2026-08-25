Theory vfmTest2108[no_sig_docs]
Ancestors vfmTestDefs2108
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs [];
val thyn = "vfmTestDefs2108";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
