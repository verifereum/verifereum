Theory vfmTest0510[no_sig_docs]
Ancestors vfmTestDefs0510
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0510_0.nsv"];
val thyn = "vfmTestDefs0510";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
