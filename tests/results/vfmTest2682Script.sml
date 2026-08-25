Theory vfmTest2682[no_sig_docs]
Ancestors vfmTestDefs2682
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2682_0.nsv", "result2682_1.nsv", "result2682_2.nsv", "result2682_3.nsv"];
val thyn = "vfmTestDefs2682";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
