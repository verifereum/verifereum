Theory vfmTest1027[no_sig_docs]
Ancestors vfmTestDefs1027
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1027_0.nsv"];
val thyn = "vfmTestDefs1027";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
