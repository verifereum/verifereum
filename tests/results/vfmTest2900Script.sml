Theory vfmTest2900[no_sig_docs]
Ancestors vfmTestDefs2900
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2900_0.nsv"];
val thyn = "vfmTestDefs2900";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
