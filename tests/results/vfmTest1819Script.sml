Theory vfmTest1819[no_sig_docs]
Ancestors vfmTestDefs1819
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1819_0.nsv", "result1819_1.nsv", "result1819_2.nsv"];
val thyn = "vfmTestDefs1819";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
