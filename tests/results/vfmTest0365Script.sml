Theory vfmTest0365[no_sig_docs]
Ancestors vfmTestDefs0365
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0365_0.nsv"];
val thyn = "vfmTestDefs0365";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
