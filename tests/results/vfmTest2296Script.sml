Theory vfmTest2296[no_sig_docs]
Ancestors vfmTestDefs2296
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2296_0.nsv", "result2296_1.nsv", "result2296_2.nsv"];
val thyn = "vfmTestDefs2296";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
