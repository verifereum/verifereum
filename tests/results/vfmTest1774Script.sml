Theory vfmTest1774[no_sig_docs]
Ancestors vfmTestDefs1774
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1774_0.nsv", "result1774_1.nsv", "result1774_2.nsv", "result1774_3.nsv", "result1774_4.nsv", "result1774_5.nsv"];
val thyn = "vfmTestDefs1774";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
