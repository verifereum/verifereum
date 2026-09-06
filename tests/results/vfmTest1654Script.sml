Theory vfmTest1654[no_sig_docs]
Ancestors vfmTestDefs1654
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1654_0.nsv", "result1654_1.nsv", "result1654_2.nsv", "result1654_3.nsv"];
val thyn = "vfmTestDefs1654";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
