Theory vfmTest2335[no_sig_docs]
Ancestors vfmTestDefs2335
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2335_0.nsv", "result2335_1.nsv", "result2335_2.nsv"];
val thyn = "vfmTestDefs2335";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
