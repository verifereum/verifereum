Theory vfmTest0997[no_sig_docs]
Ancestors vfmTestDefs0997
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0997_0.nsv", "result0997_1.nsv", "result0997_2.nsv", "result0997_3.nsv", "result0997_4.nsv", "result0997_5.nsv", "result0997_6.nsv", "result0997_7.nsv", "result0997_8.nsv", "result0997_9.nsv", "result0997_10.nsv", "result0997_11.nsv", "result0997_12.nsv", "result0997_13.nsv", "result0997_14.nsv", "result0997_15.nsv", "result0997_16.nsv", "result0997_17.nsv", "result0997_18.nsv", "result0997_19.nsv", "result0997_20.nsv", "result0997_21.nsv", "result0997_22.nsv", "result0997_23.nsv"];
val thyn = "vfmTestDefs0997";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
