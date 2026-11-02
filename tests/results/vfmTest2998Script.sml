Theory vfmTest2998[no_sig_docs]
Ancestors vfmTestDefs2998
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2998_0.nsv", "result2998_1.nsv", "result2998_2.nsv"];
val thyn = "vfmTestDefs2998";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
