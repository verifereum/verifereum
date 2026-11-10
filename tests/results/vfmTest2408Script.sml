Theory vfmTest2408[no_sig_docs]
Ancestors vfmTestDefs2408
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2408_0.nsv"];
val thyn = "vfmTestDefs2408";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
