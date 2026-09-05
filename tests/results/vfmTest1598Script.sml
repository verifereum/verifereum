Theory vfmTest1598[no_sig_docs]
Ancestors vfmTestDefs1598
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1598_0.nsv"];
val thyn = "vfmTestDefs1598";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
