Theory vfmTest2623[no_sig_docs]
Ancestors vfmTestDefs2623
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2623_0.nsv", "result2623_1.nsv", "result2623_2.nsv", "result2623_3.nsv"];
val thyn = "vfmTestDefs2623";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
