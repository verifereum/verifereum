Theory vfmTest1633[no_sig_docs]
Ancestors vfmTestDefs1633
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1633_0.nsv", "result1633_1.nsv"];
val thyn = "vfmTestDefs1633";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
