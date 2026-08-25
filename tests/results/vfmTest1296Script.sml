Theory vfmTest1296[no_sig_docs]
Ancestors vfmTestDefs1296
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1296_0.nsv"];
val thyn = "vfmTestDefs1296";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
