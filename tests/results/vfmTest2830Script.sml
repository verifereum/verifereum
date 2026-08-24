Theory vfmTest2830[no_sig_docs]
Ancestors vfmTestDefs2830
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2830_0.nsv", "result2830_1.nsv", "result2830_2.nsv", "result2830_3.nsv"];
val thyn = "vfmTestDefs2830";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
