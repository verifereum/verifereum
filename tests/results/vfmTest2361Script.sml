Theory vfmTest2361[no_sig_docs]
Ancestors vfmTestDefs2361
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2361_0.nsv"];
val thyn = "vfmTestDefs2361";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
