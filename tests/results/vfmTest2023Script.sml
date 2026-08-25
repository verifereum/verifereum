Theory vfmTest2023[no_sig_docs]
Ancestors vfmTestDefs2023
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2023_0.nsv"];
val thyn = "vfmTestDefs2023";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
