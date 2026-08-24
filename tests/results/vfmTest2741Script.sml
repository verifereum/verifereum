Theory vfmTest2741[no_sig_docs]
Ancestors vfmTestDefs2741
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2741_0.nsv", "result2741_1.nsv", "result2741_2.nsv", "result2741_3.nsv"];
val thyn = "vfmTestDefs2741";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
