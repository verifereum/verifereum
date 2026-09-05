Theory vfmTest1647[no_sig_docs]
Ancestors vfmTestDefs1647
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1647_0.nsv", "result1647_1.nsv", "result1647_2.nsv", "result1647_3.nsv", "result1647_4.nsv", "result1647_5.nsv", "result1647_6.nsv", "result1647_7.nsv", "result1647_8.nsv", "result1647_9.nsv", "result1647_10.nsv", "result1647_11.nsv", "result1647_12.nsv", "result1647_13.nsv", "result1647_14.nsv", "result1647_15.nsv", "result1647_16.nsv", "result1647_17.nsv", "result1647_18.nsv", "result1647_19.nsv", "result1647_20.nsv", "result1647_21.nsv", "result1647_22.nsv", "result1647_23.nsv", "result1647_24.nsv", "result1647_25.nsv", "result1647_26.nsv", "result1647_27.nsv", "result1647_28.nsv", "result1647_29.nsv", "result1647_30.nsv", "result1647_31.nsv"];
val thyn = "vfmTestDefs1647";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
