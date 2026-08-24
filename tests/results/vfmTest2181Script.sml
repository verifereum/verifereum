Theory vfmTest2181[no_sig_docs]
Ancestors vfmTestDefs2181
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2181_0.nsv", "result2181_1.nsv", "result2181_2.nsv", "result2181_3.nsv", "result2181_4.nsv", "result2181_5.nsv", "result2181_6.nsv", "result2181_7.nsv", "result2181_8.nsv", "result2181_9.nsv"];
val thyn = "vfmTestDefs2181";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
