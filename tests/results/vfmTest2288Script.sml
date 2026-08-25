Theory vfmTest2288[no_sig_docs]
Ancestors vfmTestDefs2288
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2288_0.nsv"];
val thyn = "vfmTestDefs2288";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
