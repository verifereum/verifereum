Theory vfmTest2923[no_sig_docs]
Ancestors vfmTestDefs2923
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2923_0.nsv", "result2923_1.nsv", "result2923_2.nsv", "result2923_3.nsv", "result2923_4.nsv"];
val thyn = "vfmTestDefs2923";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
