Theory vfmTest2680[no_sig_docs]
Ancestors vfmTestDefs2680
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2680_0.nsv", "result2680_1.nsv", "result2680_2.nsv", "result2680_3.nsv"];
val thyn = "vfmTestDefs2680";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
