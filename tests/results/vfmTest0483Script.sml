Theory vfmTest0483[no_sig_docs]
Ancestors vfmTestDefs0483
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0483_0.nsv", "result0483_1.nsv"];
val thyn = "vfmTestDefs0483";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
