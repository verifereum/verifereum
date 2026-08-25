Theory vfmTest2166[no_sig_docs]
Ancestors vfmTestDefs2166
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2166_0.nsv"];
val thyn = "vfmTestDefs2166";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
