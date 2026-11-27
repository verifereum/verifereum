Theory vfmTest1651[no_sig_docs]
Ancestors vfmTestDefs1651
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1651_0.nsv", "result1651_1.nsv", "result1651_2.nsv", "result1651_3.nsv", "result1651_4.nsv", "result1651_5.nsv", "result1651_6.nsv", "result1651_7.nsv", "result1651_8.nsv", "result1651_9.nsv", "result1651_10.nsv", "result1651_11.nsv", "result1651_12.nsv", "result1651_13.nsv", "result1651_14.nsv", "result1651_15.nsv", "result1651_16.nsv", "result1651_17.nsv", "result1651_18.nsv", "result1651_19.nsv", "result1651_20.nsv", "result1651_21.nsv", "result1651_22.nsv", "result1651_23.nsv", "result1651_24.nsv", "result1651_25.nsv", "result1651_26.nsv", "result1651_27.nsv", "result1651_28.nsv", "result1651_29.nsv", "result1651_30.nsv", "result1651_31.nsv"];
val thyn = "vfmTestDefs1651";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
