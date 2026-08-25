Theory vfmTest2796[no_sig_docs]
Ancestors vfmTestDefs2796
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2796_0.nsv", "result2796_1.nsv", "result2796_2.nsv", "result2796_3.nsv"];
val thyn = "vfmTestDefs2796";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
