Theory vfmTest2997[no_sig_docs]
Ancestors vfmTestDefs2997
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2997_0.nsv", "result2997_1.nsv", "result2997_2.nsv", "result2997_3.nsv", "result2997_4.nsv", "result2997_5.nsv", "result2997_6.nsv", "result2997_7.nsv", "result2997_8.nsv", "result2997_9.nsv", "result2997_10.nsv", "result2997_11.nsv", "result2997_12.nsv", "result2997_13.nsv", "result2997_14.nsv", "result2997_15.nsv", "result2997_16.nsv", "result2997_17.nsv", "result2997_18.nsv", "result2997_19.nsv", "result2997_20.nsv", "result2997_21.nsv", "result2997_22.nsv", "result2997_23.nsv", "result2997_24.nsv", "result2997_25.nsv", "result2997_26.nsv"];
val thyn = "vfmTestDefs2997";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
