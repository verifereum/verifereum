Theory vfmTest2773[no_sig_docs]
Ancestors vfmTestDefs2773
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2773_0.nsv", "result2773_1.nsv", "result2773_2.nsv", "result2773_3.nsv"];
val thyn = "vfmTestDefs2773";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
