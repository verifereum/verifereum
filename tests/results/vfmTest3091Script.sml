Theory vfmTest3091[no_sig_docs]
Ancestors vfmTestDefs3091
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3091_0.nsv"];
val thyn = "vfmTestDefs3091";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
