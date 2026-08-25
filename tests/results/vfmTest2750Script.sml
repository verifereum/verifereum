Theory vfmTest2750[no_sig_docs]
Ancestors vfmTestDefs2750
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2750_0.nsv", "result2750_1.nsv", "result2750_2.nsv", "result2750_3.nsv"];
val thyn = "vfmTestDefs2750";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
