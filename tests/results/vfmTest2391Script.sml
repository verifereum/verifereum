Theory vfmTest2391[no_sig_docs]
Ancestors vfmTestDefs2391
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2391_0.nsv", "result2391_1.nsv", "result2391_2.nsv", "result2391_3.nsv", "result2391_4.nsv", "result2391_5.nsv"];
val thyn = "vfmTestDefs2391";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
