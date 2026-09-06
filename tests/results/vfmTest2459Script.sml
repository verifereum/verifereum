Theory vfmTest2459[no_sig_docs]
Ancestors vfmTestDefs2459
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2459_0.nsv", "result2459_1.nsv"];
val thyn = "vfmTestDefs2459";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
