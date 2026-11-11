Theory vfmTest1547[no_sig_docs]
Ancestors vfmTestDefs1547
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1547_0.nsv", "result1547_1.nsv", "result1547_2.nsv", "result1547_3.nsv", "result1547_4.nsv", "result1547_5.nsv", "result1547_6.nsv", "result1547_7.nsv", "result1547_8.nsv", "result1547_9.nsv", "result1547_10.nsv", "result1547_11.nsv", "result1547_12.nsv", "result1547_13.nsv", "result1547_14.nsv", "result1547_15.nsv", "result1547_16.nsv", "result1547_17.nsv", "result1547_18.nsv", "result1547_19.nsv"];
val thyn = "vfmTestDefs1547";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
