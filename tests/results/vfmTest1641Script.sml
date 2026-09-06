Theory vfmTest1641[no_sig_docs]
Ancestors vfmTestDefs1641
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1641_0.nsv", "result1641_1.nsv", "result1641_2.nsv", "result1641_3.nsv", "result1641_4.nsv", "result1641_5.nsv", "result1641_6.nsv", "result1641_7.nsv"];
val thyn = "vfmTestDefs1641";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
