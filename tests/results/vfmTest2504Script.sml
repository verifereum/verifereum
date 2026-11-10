Theory vfmTest2504[no_sig_docs]
Ancestors vfmTestDefs2504
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2504_0.nsv"];
val thyn = "vfmTestDefs2504";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
