Theory vfmTest2891[no_sig_docs]
Ancestors vfmTestDefs2891
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2891_0.nsv"];
val thyn = "vfmTestDefs2891";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
