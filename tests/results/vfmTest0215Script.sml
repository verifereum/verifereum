Theory vfmTest0215[no_sig_docs]
Ancestors vfmTestDefs0215
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0215_0.nsv", "result0215_1.nsv"];
val thyn = "vfmTestDefs0215";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
