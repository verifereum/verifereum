Theory vfmTest2241[no_sig_docs]
Ancestors vfmTestDefs2241
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2241_0.nsv", "result2241_1.nsv", "result2241_2.nsv", "result2241_3.nsv"];
val thyn = "vfmTestDefs2241";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
