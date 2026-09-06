Theory vfmTest1858[no_sig_docs]
Ancestors vfmTestDefs1858
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1858_0.nsv", "result1858_1.nsv"];
val thyn = "vfmTestDefs1858";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
