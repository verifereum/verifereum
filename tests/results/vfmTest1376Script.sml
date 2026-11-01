Theory vfmTest1376[no_sig_docs]
Ancestors vfmTestDefs1376
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1376_0.nsv", "result1376_1.nsv", "result1376_2.nsv", "result1376_3.nsv", "result1376_4.nsv", "result1376_5.nsv", "result1376_6.nsv", "result1376_7.nsv"];
val thyn = "vfmTestDefs1376";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
