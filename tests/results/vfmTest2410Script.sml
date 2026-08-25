Theory vfmTest2410[no_sig_docs]
Ancestors vfmTestDefs2410
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2410_0.nsv"];
val thyn = "vfmTestDefs2410";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
