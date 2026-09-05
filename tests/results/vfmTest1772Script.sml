Theory vfmTest1772[no_sig_docs]
Ancestors vfmTestDefs1772
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1772_0.nsv", "result1772_1.nsv", "result1772_2.nsv", "result1772_3.nsv", "result1772_4.nsv", "result1772_5.nsv", "result1772_6.nsv", "result1772_7.nsv", "result1772_8.nsv", "result1772_9.nsv", "result1772_10.nsv", "result1772_11.nsv", "result1772_12.nsv", "result1772_13.nsv", "result1772_14.nsv", "result1772_15.nsv", "result1772_16.nsv", "result1772_17.nsv", "result1772_18.nsv", "result1772_19.nsv", "result1772_20.nsv", "result1772_21.nsv", "result1772_22.nsv", "result1772_23.nsv", "result1772_24.nsv", "result1772_25.nsv", "result1772_26.nsv", "result1772_27.nsv", "result1772_28.nsv", "result1772_29.nsv", "result1772_30.nsv", "result1772_31.nsv"];
val thyn = "vfmTestDefs1772";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
