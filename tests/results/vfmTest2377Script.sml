Theory vfmTest2377[no_sig_docs]
Ancestors vfmTestDefs2377
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2377_0.nsv", "result2377_1.nsv", "result2377_2.nsv", "result2377_3.nsv"];
val thyn = "vfmTestDefs2377";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
