Theory vfmTest2788[no_sig_docs]
Ancestors vfmTestDefs2788
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2788_0.nsv", "result2788_1.nsv", "result2788_2.nsv", "result2788_3.nsv"];
val thyn = "vfmTestDefs2788";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
