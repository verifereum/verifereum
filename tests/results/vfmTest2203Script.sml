Theory vfmTest2203[no_sig_docs]
Ancestors vfmTestDefs2203
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2203_0.nsv", "result2203_1.nsv", "result2203_2.nsv", "result2203_3.nsv", "result2203_4.nsv", "result2203_5.nsv", "result2203_6.nsv", "result2203_7.nsv", "result2203_8.nsv", "result2203_9.nsv", "result2203_10.nsv", "result2203_11.nsv"];
val thyn = "vfmTestDefs2203";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
