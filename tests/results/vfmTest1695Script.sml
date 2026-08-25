Theory vfmTest1695[no_sig_docs]
Ancestors vfmTestDefs1695
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1695_0.nsv"];
val thyn = "vfmTestDefs1695";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
