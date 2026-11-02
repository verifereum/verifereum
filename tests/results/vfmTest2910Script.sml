Theory vfmTest2910[no_sig_docs]
Ancestors vfmTestDefs2910
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2910_0.nsv"];
val thyn = "vfmTestDefs2910";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
