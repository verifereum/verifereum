Theory vfmTest2890[no_sig_docs]
Ancestors vfmTestDefs2890
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2890_0.nsv"];
val thyn = "vfmTestDefs2890";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
