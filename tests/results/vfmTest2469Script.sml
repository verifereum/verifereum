Theory vfmTest2469[no_sig_docs]
Ancestors vfmTestDefs2469
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2469_0.nsv", "result2469_1.nsv", "result2469_2.nsv", "result2469_3.nsv", "result2469_4.nsv"];
val thyn = "vfmTestDefs2469";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
