Theory vfmTest2641[no_sig_docs]
Ancestors vfmTestDefs2641
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2641_0.nsv", "result2641_1.nsv", "result2641_2.nsv", "result2641_3.nsv"];
val thyn = "vfmTestDefs2641";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
