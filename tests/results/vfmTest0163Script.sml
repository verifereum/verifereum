Theory vfmTest0163[no_sig_docs]
Ancestors vfmTestDefs0163
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0163_0.nsv"];
val thyn = "vfmTestDefs0163";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
