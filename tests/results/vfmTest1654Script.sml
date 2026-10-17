Theory vfmTest1654[no_sig_docs]
Ancestors vfmTestDefs1654
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1654_0.nsv", "result1654_1.nsv", "result1654_2.nsv", "result1654_3.nsv", "result1654_4.nsv", "result1654_5.nsv", "result1654_6.nsv", "result1654_7.nsv", "result1654_8.nsv", "result1654_9.nsv", "result1654_10.nsv", "result1654_11.nsv", "result1654_12.nsv", "result1654_13.nsv", "result1654_14.nsv", "result1654_15.nsv", "result1654_16.nsv", "result1654_17.nsv", "result1654_18.nsv", "result1654_19.nsv"];
val thyn = "vfmTestDefs1654";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
