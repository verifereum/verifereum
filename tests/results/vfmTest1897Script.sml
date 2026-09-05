Theory vfmTest1897[no_sig_docs]
Ancestors vfmTestDefs1897
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1897_0.nsv", "result1897_1.nsv"];
val thyn = "vfmTestDefs1897";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
