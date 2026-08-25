Theory vfmTest2697[no_sig_docs]
Ancestors vfmTestDefs2697
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2697_0.nsv", "result2697_1.nsv", "result2697_2.nsv", "result2697_3.nsv"];
val thyn = "vfmTestDefs2697";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
