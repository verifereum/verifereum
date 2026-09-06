Theory vfmTest1627[no_sig_docs]
Ancestors vfmTestDefs1627
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1627_0.nsv", "result1627_1.nsv", "result1627_2.nsv", "result1627_3.nsv", "result1627_4.nsv", "result1627_5.nsv", "result1627_6.nsv", "result1627_7.nsv", "result1627_8.nsv", "result1627_9.nsv", "result1627_10.nsv", "result1627_11.nsv", "result1627_12.nsv", "result1627_13.nsv", "result1627_14.nsv", "result1627_15.nsv", "result1627_16.nsv", "result1627_17.nsv", "result1627_18.nsv", "result1627_19.nsv", "result1627_20.nsv", "result1627_21.nsv", "result1627_22.nsv", "result1627_23.nsv"];
val thyn = "vfmTestDefs1627";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
