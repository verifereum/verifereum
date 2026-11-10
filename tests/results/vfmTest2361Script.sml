Theory vfmTest2361[no_sig_docs]
Ancestors vfmTestDefs2361
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2361_0.nsv", "result2361_1.nsv", "result2361_2.nsv", "result2361_3.nsv", "result2361_4.nsv", "result2361_5.nsv", "result2361_6.nsv", "result2361_7.nsv", "result2361_8.nsv", "result2361_9.nsv", "result2361_10.nsv", "result2361_11.nsv"];
val thyn = "vfmTestDefs2361";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
