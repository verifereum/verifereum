Theory vfmTest2348[no_sig_docs]
Ancestors vfmTestDefs2348
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2348_0.nsv", "result2348_1.nsv", "result2348_2.nsv", "result2348_3.nsv", "result2348_4.nsv", "result2348_5.nsv", "result2348_6.nsv", "result2348_7.nsv", "result2348_8.nsv", "result2348_9.nsv", "result2348_10.nsv", "result2348_11.nsv", "result2348_12.nsv", "result2348_13.nsv", "result2348_14.nsv", "result2348_15.nsv", "result2348_16.nsv", "result2348_17.nsv", "result2348_18.nsv", "result2348_19.nsv", "result2348_20.nsv", "result2348_21.nsv", "result2348_22.nsv", "result2348_23.nsv", "result2348_24.nsv", "result2348_25.nsv", "result2348_26.nsv", "result2348_27.nsv", "result2348_28.nsv", "result2348_29.nsv", "result2348_30.nsv", "result2348_31.nsv", "result2348_32.nsv", "result2348_33.nsv", "result2348_34.nsv", "result2348_35.nsv", "result2348_36.nsv", "result2348_37.nsv", "result2348_38.nsv", "result2348_39.nsv"];
val thyn = "vfmTestDefs2348";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
