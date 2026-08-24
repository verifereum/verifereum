Theory vfmTest0231[no_sig_docs]
Ancestors vfmTestDefs0231
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0231_0.nsv", "result0231_1.nsv", "result0231_2.nsv", "result0231_3.nsv", "result0231_4.nsv", "result0231_5.nsv", "result0231_6.nsv", "result0231_7.nsv", "result0231_8.nsv", "result0231_9.nsv", "result0231_10.nsv", "result0231_11.nsv", "result0231_12.nsv", "result0231_13.nsv", "result0231_14.nsv", "result0231_15.nsv", "result0231_16.nsv", "result0231_17.nsv", "result0231_18.nsv", "result0231_19.nsv", "result0231_20.nsv", "result0231_21.nsv", "result0231_22.nsv", "result0231_23.nsv", "result0231_24.nsv", "result0231_25.nsv", "result0231_26.nsv", "result0231_27.nsv", "result0231_28.nsv", "result0231_29.nsv", "result0231_30.nsv", "result0231_31.nsv", "result0231_32.nsv", "result0231_33.nsv", "result0231_34.nsv", "result0231_35.nsv", "result0231_36.nsv", "result0231_37.nsv", "result0231_38.nsv", "result0231_39.nsv", "result0231_40.nsv", "result0231_41.nsv", "result0231_42.nsv", "result0231_43.nsv", "result0231_44.nsv", "result0231_45.nsv", "result0231_46.nsv", "result0231_47.nsv", "result0231_48.nsv", "result0231_49.nsv", "result0231_50.nsv", "result0231_51.nsv"];
val thyn = "vfmTestDefs0231";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
