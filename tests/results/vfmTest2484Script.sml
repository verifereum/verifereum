Theory vfmTest2484[no_sig_docs]
Ancestors vfmTestDefs2484
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2484_0.nsv"];
val thyn = "vfmTestDefs2484";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
