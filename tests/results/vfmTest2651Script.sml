Theory vfmTest2651[no_sig_docs]
Ancestors vfmTestDefs2651
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2651_0.nsv", "result2651_1.nsv", "result2651_2.nsv", "result2651_3.nsv"];
val thyn = "vfmTestDefs2651";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
