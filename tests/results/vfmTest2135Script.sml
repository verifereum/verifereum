Theory vfmTest2135[no_sig_docs]
Ancestors vfmTestDefs2135
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2135_0.nsv", "result2135_1.nsv", "result2135_2.nsv", "result2135_3.nsv", "result2135_4.nsv", "result2135_5.nsv", "result2135_6.nsv", "result2135_7.nsv", "result2135_8.nsv", "result2135_9.nsv"];
val thyn = "vfmTestDefs2135";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
