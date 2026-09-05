Theory vfmTest2270[no_sig_docs]
Ancestors vfmTestDefs2270
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2270_0.nsv", "result2270_1.nsv", "result2270_2.nsv", "result2270_3.nsv", "result2270_4.nsv", "result2270_5.nsv"];
val thyn = "vfmTestDefs2270";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
