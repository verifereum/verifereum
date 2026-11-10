Theory vfmTest0796[no_sig_docs]
Ancestors vfmTestDefs0796
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0796_0.nsv", "result0796_1.nsv"];
val thyn = "vfmTestDefs0796";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
