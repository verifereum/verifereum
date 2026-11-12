Theory vfmTest1636[no_sig_docs]
Ancestors vfmTestDefs1636
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1636_0.nsv", "result1636_1.nsv", "result1636_2.nsv", "result1636_3.nsv", "result1636_4.nsv", "result1636_5.nsv", "result1636_6.nsv", "result1636_7.nsv", "result1636_8.nsv", "result1636_9.nsv", "result1636_10.nsv", "result1636_11.nsv", "result1636_12.nsv", "result1636_13.nsv", "result1636_14.nsv", "result1636_15.nsv", "result1636_16.nsv", "result1636_17.nsv", "result1636_18.nsv", "result1636_19.nsv", "result1636_20.nsv", "result1636_21.nsv", "result1636_22.nsv", "result1636_23.nsv", "result1636_24.nsv", "result1636_25.nsv", "result1636_26.nsv", "result1636_27.nsv", "result1636_28.nsv", "result1636_29.nsv", "result1636_30.nsv", "result1636_31.nsv"];
val thyn = "vfmTestDefs1636";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
