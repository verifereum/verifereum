Theory vfmTest0517[no_sig_docs]
Ancestors vfmTestDefs0517
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0517_0.nsv", "result0517_1.nsv"];
val thyn = "vfmTestDefs0517";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
