Theory vfmTest1293[no_sig_docs]
Ancestors vfmTestDefs1293
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1293_0.nsv", "result1293_1.nsv", "result1293_2.nsv", "result1293_3.nsv", "result1293_4.nsv", "result1293_5.nsv"];
val thyn = "vfmTestDefs1293";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
