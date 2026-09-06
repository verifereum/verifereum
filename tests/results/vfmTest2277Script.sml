Theory vfmTest2277[no_sig_docs]
Ancestors vfmTestDefs2277
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2277_0.nsv", "result2277_1.nsv", "result2277_2.nsv", "result2277_3.nsv", "result2277_4.nsv", "result2277_5.nsv"];
val thyn = "vfmTestDefs2277";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
