Theory vfmTest1037[no_sig_docs]
Ancestors vfmTestDefs1037
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1037_0.nsv", "result1037_1.nsv", "result1037_2.nsv", "result1037_3.nsv", "result1037_4.nsv", "result1037_5.nsv", "result1037_6.nsv", "result1037_7.nsv", "result1037_8.nsv", "result1037_9.nsv", "result1037_10.nsv", "result1037_11.nsv", "result1037_12.nsv", "result1037_13.nsv", "result1037_14.nsv", "result1037_15.nsv", "result1037_16.nsv", "result1037_17.nsv"];
val thyn = "vfmTestDefs1037";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
