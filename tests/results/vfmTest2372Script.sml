Theory vfmTest2372[no_sig_docs]
Ancestors vfmTestDefs2372
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2372_0.nsv", "result2372_1.nsv", "result2372_2.nsv", "result2372_3.nsv", "result2372_4.nsv", "result2372_5.nsv", "result2372_6.nsv", "result2372_7.nsv"];
val thyn = "vfmTestDefs2372";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
