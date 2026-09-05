Theory vfmTest0144[no_sig_docs]
Ancestors vfmTestDefs0144
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0144_0.nsv", "result0144_1.nsv"];
val thyn = "vfmTestDefs0144";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
