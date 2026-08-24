Theory vfmTest2733[no_sig_docs]
Ancestors vfmTestDefs2733
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2733_0.nsv", "result2733_1.nsv", "result2733_2.nsv", "result2733_3.nsv"];
val thyn = "vfmTestDefs2733";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
