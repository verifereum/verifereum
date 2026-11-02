Theory vfmTest1481[no_sig_docs]
Ancestors vfmTestDefs1481
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1481_0.nsv", "result1481_1.nsv", "result1481_2.nsv", "result1481_3.nsv", "result1481_4.nsv", "result1481_5.nsv", "result1481_6.nsv", "result1481_7.nsv"];
val thyn = "vfmTestDefs1481";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
