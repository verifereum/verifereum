Theory vfmTest2705[no_sig_docs]
Ancestors vfmTestDefs2705
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2705_0.nsv"];
val thyn = "vfmTestDefs2705";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
