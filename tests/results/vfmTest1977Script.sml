Theory vfmTest1977[no_sig_docs]
Ancestors vfmTestDefs1977
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1977_0.nsv", "result1977_1.nsv"];
val thyn = "vfmTestDefs1977";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
