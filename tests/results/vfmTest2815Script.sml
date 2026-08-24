Theory vfmTest2815[no_sig_docs]
Ancestors vfmTestDefs2815
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2815_0.nsv", "result2815_1.nsv", "result2815_2.nsv", "result2815_3.nsv"];
val thyn = "vfmTestDefs2815";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
