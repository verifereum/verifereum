Theory vfmTest2391[no_sig_docs]
Ancestors vfmTestDefs2391
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2391_0.nsv", "result2391_1.nsv", "result2391_2.nsv", "result2391_3.nsv", "result2391_4.nsv", "result2391_5.nsv", "result2391_6.nsv", "result2391_7.nsv", "result2391_8.nsv", "result2391_9.nsv", "result2391_10.nsv", "result2391_11.nsv", "result2391_12.nsv", "result2391_13.nsv", "result2391_14.nsv", "result2391_15.nsv"];
val thyn = "vfmTestDefs2391";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
