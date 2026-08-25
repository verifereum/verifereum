Theory vfmTest2341[no_sig_docs]
Ancestors vfmTestDefs2341
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2341_0.nsv", "result2341_1.nsv", "result2341_2.nsv"];
val thyn = "vfmTestDefs2341";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
