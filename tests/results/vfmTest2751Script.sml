Theory vfmTest2751[no_sig_docs]
Ancestors vfmTestDefs2751
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2751_0.nsv", "result2751_1.nsv", "result2751_2.nsv", "result2751_3.nsv"];
val thyn = "vfmTestDefs2751";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
