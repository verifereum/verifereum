Theory vfmTest2454[no_sig_docs]
Ancestors vfmTestDefs2454
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2454_0.nsv"];
val thyn = "vfmTestDefs2454";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
