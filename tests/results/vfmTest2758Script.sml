Theory vfmTest2758[no_sig_docs]
Ancestors vfmTestDefs2758
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2758_0.nsv", "result2758_1.nsv", "result2758_2.nsv", "result2758_3.nsv"];
val thyn = "vfmTestDefs2758";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
