Theory vfmTest0268[no_sig_docs]
Ancestors vfmTestDefs0268
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0268_0.nsv"];
val thyn = "vfmTestDefs0268";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
