Theory vfmTest2885[no_sig_docs]
Ancestors vfmTestDefs2885
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2885_0.nsv"];
val thyn = "vfmTestDefs2885";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
