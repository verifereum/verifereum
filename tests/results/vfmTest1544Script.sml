Theory vfmTest1544[no_sig_docs]
Ancestors vfmTestDefs1544
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1544_0.nsv", "result1544_1.nsv", "result1544_2.nsv", "result1544_3.nsv", "result1544_4.nsv", "result1544_5.nsv", "result1544_6.nsv", "result1544_7.nsv", "result1544_8.nsv", "result1544_9.nsv", "result1544_10.nsv", "result1544_11.nsv", "result1544_12.nsv", "result1544_13.nsv", "result1544_14.nsv", "result1544_15.nsv", "result1544_16.nsv", "result1544_17.nsv", "result1544_18.nsv", "result1544_19.nsv"];
val thyn = "vfmTestDefs1544";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
