Theory vfmTest0140[no_sig_docs]
Ancestors vfmTestDefs0140
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0140_0.nsv", "result0140_1.nsv", "result0140_2.nsv", "result0140_3.nsv", "result0140_4.nsv", "result0140_5.nsv", "result0140_6.nsv", "result0140_7.nsv", "result0140_8.nsv", "result0140_9.nsv", "result0140_10.nsv", "result0140_11.nsv", "result0140_12.nsv", "result0140_13.nsv", "result0140_14.nsv", "result0140_15.nsv", "result0140_16.nsv", "result0140_17.nsv", "result0140_18.nsv", "result0140_19.nsv", "result0140_20.nsv", "result0140_21.nsv", "result0140_22.nsv", "result0140_23.nsv", "result0140_24.nsv", "result0140_25.nsv", "result0140_26.nsv", "result0140_27.nsv", "result0140_28.nsv", "result0140_29.nsv", "result0140_30.nsv", "result0140_31.nsv", "result0140_32.nsv", "result0140_33.nsv", "result0140_34.nsv", "result0140_35.nsv", "result0140_36.nsv", "result0140_37.nsv", "result0140_38.nsv", "result0140_39.nsv", "result0140_40.nsv", "result0140_41.nsv", "result0140_42.nsv", "result0140_43.nsv", "result0140_44.nsv", "result0140_45.nsv", "result0140_46.nsv", "result0140_47.nsv"];
val thyn = "vfmTestDefs0140";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
