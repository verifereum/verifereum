Theory vfmTest2133[no_sig_docs]
Ancestors vfmTestDefs2133
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2133_0.nsv"];
val thyn = "vfmTestDefs2133";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
