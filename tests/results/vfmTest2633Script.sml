Theory vfmTest2633[no_sig_docs]
Ancestors vfmTestDefs2633
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2633_0.nsv", "result2633_1.nsv", "result2633_2.nsv", "result2633_3.nsv"];
val thyn = "vfmTestDefs2633";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
