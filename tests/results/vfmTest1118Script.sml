Theory vfmTest1118[no_sig_docs]
Ancestors vfmTestDefs1118
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1118_0.nsv", "result1118_1.nsv"];
val thyn = "vfmTestDefs1118";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
