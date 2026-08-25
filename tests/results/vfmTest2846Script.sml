Theory vfmTest2846[no_sig_docs]
Ancestors vfmTestDefs2846
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2846_0.nsv", "result2846_1.nsv", "result2846_2.nsv", "result2846_3.nsv"];
val thyn = "vfmTestDefs2846";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
