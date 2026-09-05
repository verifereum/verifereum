Theory vfmTest0525[no_sig_docs]
Ancestors vfmTestDefs0525
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0525_0.nsv"];
val thyn = "vfmTestDefs0525";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
