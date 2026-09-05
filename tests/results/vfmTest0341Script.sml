Theory vfmTest0341[no_sig_docs]
Ancestors vfmTestDefs0341
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0341_0.nsv", "result0341_1.nsv"];
val thyn = "vfmTestDefs0341";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
