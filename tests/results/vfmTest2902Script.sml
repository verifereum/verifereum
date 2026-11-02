Theory vfmTest2902[no_sig_docs]
Ancestors vfmTestDefs2902
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2902_0.nsv"];
val thyn = "vfmTestDefs2902";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
