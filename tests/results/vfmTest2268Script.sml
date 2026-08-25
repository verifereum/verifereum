Theory vfmTest2268[no_sig_docs]
Ancestors vfmTestDefs2268
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2268_0.nsv", "result2268_1.nsv"];
val thyn = "vfmTestDefs2268";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
