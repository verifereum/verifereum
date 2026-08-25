Theory vfmTest2559[no_sig_docs]
Ancestors vfmTestDefs2559
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2559_0.nsv"];
val thyn = "vfmTestDefs2559";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
