Theory vfmTest1047[no_sig_docs]
Ancestors vfmTestDefs1047
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1047_0.nsv"];
val thyn = "vfmTestDefs1047";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
