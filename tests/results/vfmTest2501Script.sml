Theory vfmTest2501[no_sig_docs]
Ancestors vfmTestDefs2501
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2501_0.nsv"];
val thyn = "vfmTestDefs2501";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
