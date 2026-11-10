Theory vfmTest3142[no_sig_docs]
Ancestors vfmTestDefs3142
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3142_0.nsv", "result3142_1.nsv", "result3142_2.nsv", "result3142_3.nsv", "result3142_4.nsv", "result3142_5.nsv", "result3142_6.nsv", "result3142_7.nsv", "result3142_8.nsv", "result3142_9.nsv", "result3142_10.nsv", "result3142_11.nsv", "result3142_12.nsv", "result3142_13.nsv", "result3142_14.nsv", "result3142_15.nsv", "result3142_16.nsv", "result3142_17.nsv", "result3142_18.nsv", "result3142_19.nsv", "result3142_20.nsv", "result3142_21.nsv", "result3142_22.nsv", "result3142_23.nsv", "result3142_24.nsv", "result3142_25.nsv", "result3142_26.nsv", "result3142_27.nsv", "result3142_28.nsv", "result3142_29.nsv", "result3142_30.nsv", "result3142_31.nsv", "result3142_32.nsv", "result3142_33.nsv", "result3142_34.nsv", "result3142_35.nsv", "result3142_36.nsv", "result3142_37.nsv", "result3142_38.nsv", "result3142_39.nsv"];
val thyn = "vfmTestDefs3142";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
