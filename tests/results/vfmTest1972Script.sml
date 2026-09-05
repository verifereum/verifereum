Theory vfmTest1972[no_sig_docs]
Ancestors vfmTestDefs1972
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1972_0.nsv", "result1972_1.nsv"];
val thyn = "vfmTestDefs1972";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
