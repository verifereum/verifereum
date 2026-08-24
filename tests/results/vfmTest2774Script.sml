Theory vfmTest2774[no_sig_docs]
Ancestors vfmTestDefs2774
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2774_0.nsv", "result2774_1.nsv", "result2774_2.nsv", "result2774_3.nsv"];
val thyn = "vfmTestDefs2774";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
