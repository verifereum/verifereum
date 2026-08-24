Theory vfmTest2389[no_sig_docs]
Ancestors vfmTestDefs2389
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2389_0.nsv"];
val thyn = "vfmTestDefs2389";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
