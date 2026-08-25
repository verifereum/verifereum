Theory vfmTest2579[no_sig_docs]
Ancestors vfmTestDefs2579
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2579_0.nsv"];
val thyn = "vfmTestDefs2579";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
