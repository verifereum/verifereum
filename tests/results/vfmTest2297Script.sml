Theory vfmTest2297[no_sig_docs]
Ancestors vfmTestDefs2297
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2297_0.nsv", "result2297_1.nsv", "result2297_2.nsv", "result2297_3.nsv", "result2297_4.nsv", "result2297_5.nsv", "result2297_6.nsv", "result2297_7.nsv", "result2297_8.nsv", "result2297_9.nsv", "result2297_10.nsv", "result2297_11.nsv"];
val thyn = "vfmTestDefs2297";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
