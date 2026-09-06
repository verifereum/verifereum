Theory vfmTest0440[no_sig_docs]
Ancestors vfmTestDefs0440
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0440_0.nsv"];
val thyn = "vfmTestDefs0440";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
