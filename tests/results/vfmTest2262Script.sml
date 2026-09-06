Theory vfmTest2262[no_sig_docs]
Ancestors vfmTestDefs2262
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2262_0.nsv", "result2262_1.nsv", "result2262_2.nsv", "result2262_3.nsv", "result2262_4.nsv", "result2262_5.nsv", "result2262_6.nsv", "result2262_7.nsv", "result2262_8.nsv"];
val thyn = "vfmTestDefs2262";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
