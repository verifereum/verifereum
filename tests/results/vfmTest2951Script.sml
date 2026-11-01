Theory vfmTest2951[no_sig_docs]
Ancestors vfmTestDefs2951
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2951_0.nsv", "result2951_1.nsv", "result2951_2.nsv", "result2951_3.nsv"];
val thyn = "vfmTestDefs2951";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
