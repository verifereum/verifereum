Theory vfmTest2617[no_sig_docs]
Ancestors vfmTestDefs2617
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2617_0.nsv", "result2617_1.nsv", "result2617_2.nsv", "result2617_3.nsv"];
val thyn = "vfmTestDefs2617";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
