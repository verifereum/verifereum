Theory vfmTest0709[no_sig_docs]
Ancestors vfmTestDefs0709
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0709_0.nsv"];
val thyn = "vfmTestDefs0709";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
