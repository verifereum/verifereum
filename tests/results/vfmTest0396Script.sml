Theory vfmTest0396[no_sig_docs]
Ancestors vfmTestDefs0396
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0396_0.nsv"];
val thyn = "vfmTestDefs0396";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
