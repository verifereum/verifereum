Theory vfmTest2612[no_sig_docs]
Ancestors vfmTestDefs2612
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2612_0.nsv", "result2612_1.nsv", "result2612_2.nsv", "result2612_3.nsv"];
val thyn = "vfmTestDefs2612";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
