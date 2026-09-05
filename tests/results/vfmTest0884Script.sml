Theory vfmTest0884[no_sig_docs]
Ancestors vfmTestDefs0884
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0884_0.nsv", "result0884_1.nsv"];
val thyn = "vfmTestDefs0884";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
