Theory vfmTest2787[no_sig_docs]
Ancestors vfmTestDefs2787
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2787_0.nsv", "result2787_1.nsv", "result2787_2.nsv", "result2787_3.nsv"];
val thyn = "vfmTestDefs2787";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
