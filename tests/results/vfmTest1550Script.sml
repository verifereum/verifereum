Theory vfmTest1550[no_sig_docs]
Ancestors vfmTestDefs1550
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1550_0.nsv", "result1550_1.nsv", "result1550_2.nsv", "result1550_3.nsv", "result1550_4.nsv", "result1550_5.nsv", "result1550_6.nsv", "result1550_7.nsv", "result1550_8.nsv", "result1550_9.nsv", "result1550_10.nsv", "result1550_11.nsv", "result1550_12.nsv", "result1550_13.nsv", "result1550_14.nsv", "result1550_15.nsv", "result1550_16.nsv", "result1550_17.nsv", "result1550_18.nsv", "result1550_19.nsv"];
val thyn = "vfmTestDefs1550";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
