Theory vfmTest1057[no_sig_docs]
Ancestors vfmTestDefs1057
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1057_0.nsv", "result1057_1.nsv", "result1057_2.nsv", "result1057_3.nsv"];
val thyn = "vfmTestDefs1057";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
