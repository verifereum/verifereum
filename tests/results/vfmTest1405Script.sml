Theory vfmTest1405[no_sig_docs]
Ancestors vfmTestDefs1405
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1405_0.nsv", "result1405_1.nsv", "result1405_2.nsv", "result1405_3.nsv", "result1405_4.nsv", "result1405_5.nsv", "result1405_6.nsv", "result1405_7.nsv", "result1405_8.nsv", "result1405_9.nsv", "result1405_10.nsv", "result1405_11.nsv", "result1405_12.nsv", "result1405_13.nsv", "result1405_14.nsv", "result1405_15.nsv", "result1405_16.nsv", "result1405_17.nsv", "result1405_18.nsv", "result1405_19.nsv", "result1405_20.nsv", "result1405_21.nsv", "result1405_22.nsv", "result1405_23.nsv"];
val thyn = "vfmTestDefs1405";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
