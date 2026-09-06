Theory vfmTest2024[no_sig_docs]
Ancestors vfmTestDefs2024
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2024_0.nsv", "result2024_1.nsv"];
val thyn = "vfmTestDefs2024";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
