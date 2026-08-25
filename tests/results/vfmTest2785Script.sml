Theory vfmTest2785[no_sig_docs]
Ancestors vfmTestDefs2785
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2785_0.nsv", "result2785_1.nsv", "result2785_2.nsv", "result2785_3.nsv"];
val thyn = "vfmTestDefs2785";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
