Theory vfmTest0275[no_sig_docs]
Ancestors vfmTestDefs0275
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0275_0.nsv", "result0275_1.nsv", "result0275_2.nsv", "result0275_3.nsv", "result0275_4.nsv", "result0275_5.nsv", "result0275_6.nsv", "result0275_7.nsv", "result0275_8.nsv", "result0275_9.nsv", "result0275_10.nsv", "result0275_11.nsv", "result0275_12.nsv", "result0275_13.nsv", "result0275_14.nsv", "result0275_15.nsv", "result0275_16.nsv", "result0275_17.nsv", "result0275_18.nsv", "result0275_19.nsv", "result0275_20.nsv", "result0275_21.nsv", "result0275_22.nsv", "result0275_23.nsv", "result0275_24.nsv", "result0275_25.nsv", "result0275_26.nsv", "result0275_27.nsv", "result0275_28.nsv", "result0275_29.nsv", "result0275_30.nsv", "result0275_31.nsv", "result0275_32.nsv", "result0275_33.nsv", "result0275_34.nsv", "result0275_35.nsv", "result0275_36.nsv", "result0275_37.nsv", "result0275_38.nsv", "result0275_39.nsv", "result0275_40.nsv", "result0275_41.nsv", "result0275_42.nsv", "result0275_43.nsv", "result0275_44.nsv", "result0275_45.nsv"];
val thyn = "vfmTestDefs0275";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
