Theory vfmTest2135[no_sig_docs]
Ancestors vfmTestDefs2135
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2135_0.nsv"];
val thyn = "vfmTestDefs2135";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
