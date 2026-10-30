Theory vfmTest1294[no_sig_docs]
Ancestors vfmTestDefs1294
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1294_0.nsv", "result1294_1.nsv", "result1294_2.nsv", "result1294_3.nsv", "result1294_4.nsv", "result1294_5.nsv", "result1294_6.nsv", "result1294_7.nsv", "result1294_8.nsv", "result1294_9.nsv", "result1294_10.nsv", "result1294_11.nsv"];
val thyn = "vfmTestDefs1294";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
