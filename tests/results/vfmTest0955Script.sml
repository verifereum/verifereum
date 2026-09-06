Theory vfmTest0955[no_sig_docs]
Ancestors vfmTestDefs0955
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0955_0.nsv"];
val thyn = "vfmTestDefs0955";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
