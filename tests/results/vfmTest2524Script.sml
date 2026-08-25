Theory vfmTest2524[no_sig_docs]
Ancestors vfmTestDefs2524
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2524_0.nsv"];
val thyn = "vfmTestDefs2524";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
