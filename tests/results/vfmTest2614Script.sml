Theory vfmTest2614[no_sig_docs]
Ancestors vfmTestDefs2614
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2614_0.nsv", "result2614_1.nsv", "result2614_2.nsv", "result2614_3.nsv"];
val thyn = "vfmTestDefs2614";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
