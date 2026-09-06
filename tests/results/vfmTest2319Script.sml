Theory vfmTest2319[no_sig_docs]
Ancestors vfmTestDefs2319
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2319_0.nsv", "result2319_1.nsv", "result2319_2.nsv", "result2319_3.nsv"];
val thyn = "vfmTestDefs2319";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
