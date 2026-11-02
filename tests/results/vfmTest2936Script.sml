Theory vfmTest2936[no_sig_docs]
Ancestors vfmTestDefs2936
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2936_0.nsv"];
val thyn = "vfmTestDefs2936";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
