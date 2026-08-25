Theory vfmTest2805[no_sig_docs]
Ancestors vfmTestDefs2805
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2805_0.nsv", "result2805_1.nsv", "result2805_2.nsv", "result2805_3.nsv"];
val thyn = "vfmTestDefs2805";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
