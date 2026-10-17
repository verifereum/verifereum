Theory vfmTest2239[no_sig_docs]
Ancestors vfmTestDefs2239
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2239_0.nsv", "result2239_1.nsv", "result2239_2.nsv", "result2239_3.nsv", "result2239_4.nsv", "result2239_5.nsv", "result2239_6.nsv", "result2239_7.nsv", "result2239_8.nsv", "result2239_9.nsv"];
val thyn = "vfmTestDefs2239";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
