Theory vfmTest2861[no_sig_docs]
Ancestors vfmTestDefs2861
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2861_0.nsv"];
val thyn = "vfmTestDefs2861";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
