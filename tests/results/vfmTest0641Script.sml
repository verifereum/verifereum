Theory vfmTest0641[no_sig_docs]
Ancestors vfmTestDefs0641
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0641_0.nsv"];
val thyn = "vfmTestDefs0641";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
