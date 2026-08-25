Theory vfmTest2402[no_sig_docs]
Ancestors vfmTestDefs2402
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2402_0.nsv"];
val thyn = "vfmTestDefs2402";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
