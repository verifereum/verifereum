Theory vfmTest0941[no_sig_docs]
Ancestors vfmTestDefs0941
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0941_0.nsv"];
val thyn = "vfmTestDefs0941";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
