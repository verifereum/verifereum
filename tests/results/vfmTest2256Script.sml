Theory vfmTest2256[no_sig_docs]
Ancestors vfmTestDefs2256
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2256_0.nsv", "result2256_1.nsv"];
val thyn = "vfmTestDefs2256";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
