Theory vfmTest1210[no_sig_docs]
Ancestors vfmTestDefs1210
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1210_0.nsv", "result1210_1.nsv", "result1210_2.nsv", "result1210_3.nsv", "result1210_4.nsv", "result1210_5.nsv", "result1210_6.nsv", "result1210_7.nsv", "result1210_8.nsv", "result1210_9.nsv", "result1210_10.nsv", "result1210_11.nsv", "result1210_12.nsv", "result1210_13.nsv", "result1210_14.nsv", "result1210_15.nsv", "result1210_16.nsv", "result1210_17.nsv", "result1210_18.nsv", "result1210_19.nsv", "result1210_20.nsv", "result1210_21.nsv", "result1210_22.nsv", "result1210_23.nsv", "result1210_24.nsv", "result1210_25.nsv", "result1210_26.nsv", "result1210_27.nsv", "result1210_28.nsv", "result1210_29.nsv", "result1210_30.nsv", "result1210_31.nsv", "result1210_32.nsv", "result1210_33.nsv", "result1210_34.nsv", "result1210_35.nsv", "result1210_36.nsv", "result1210_37.nsv", "result1210_38.nsv", "result1210_39.nsv", "result1210_40.nsv", "result1210_41.nsv"];
val thyn = "vfmTestDefs1210";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
