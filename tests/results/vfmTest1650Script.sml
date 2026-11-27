Theory vfmTest1650[no_sig_docs]
Ancestors vfmTestDefs1650
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1650_0.nsv", "result1650_1.nsv", "result1650_2.nsv", "result1650_3.nsv", "result1650_4.nsv", "result1650_5.nsv", "result1650_6.nsv", "result1650_7.nsv", "result1650_8.nsv", "result1650_9.nsv", "result1650_10.nsv", "result1650_11.nsv", "result1650_12.nsv", "result1650_13.nsv", "result1650_14.nsv", "result1650_15.nsv", "result1650_16.nsv", "result1650_17.nsv", "result1650_18.nsv", "result1650_19.nsv", "result1650_20.nsv", "result1650_21.nsv", "result1650_22.nsv", "result1650_23.nsv", "result1650_24.nsv", "result1650_25.nsv", "result1650_26.nsv", "result1650_27.nsv", "result1650_28.nsv", "result1650_29.nsv", "result1650_30.nsv", "result1650_31.nsv"];
val thyn = "vfmTestDefs1650";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
