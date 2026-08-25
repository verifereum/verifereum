Theory vfmTest2257[no_sig_docs]
Ancestors vfmTestDefs2257
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2257_0.nsv", "result2257_1.nsv"];
val thyn = "vfmTestDefs2257";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
