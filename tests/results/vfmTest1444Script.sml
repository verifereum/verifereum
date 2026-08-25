Theory vfmTest1444[no_sig_docs]
Ancestors vfmTestDefs1444
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1444_0.nsv"];
val thyn = "vfmTestDefs1444";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
