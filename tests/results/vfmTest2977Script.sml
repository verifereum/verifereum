Theory vfmTest2977[no_sig_docs]
Ancestors vfmTestDefs2977
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2977_0.nsv", "result2977_1.nsv"];
val thyn = "vfmTestDefs2977";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
