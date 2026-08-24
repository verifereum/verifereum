Theory vfmTest2469[no_sig_docs]
Ancestors vfmTestDefs2469
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2469_0.nsv"];
val thyn = "vfmTestDefs2469";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
