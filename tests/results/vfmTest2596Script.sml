Theory vfmTest2596[no_sig_docs]
Ancestors vfmTestDefs2596
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2596_0.nsv", "result2596_1.nsv", "result2596_2.nsv", "result2596_3.nsv"];
val thyn = "vfmTestDefs2596";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
