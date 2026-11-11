Theory vfmTest0835[no_sig_docs]
Ancestors vfmTestDefs0835
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0835_0.nsv", "result0835_1.nsv", "result0835_2.nsv", "result0835_3.nsv", "result0835_4.nsv", "result0835_5.nsv", "result0835_6.nsv", "result0835_7.nsv", "result0835_8.nsv", "result0835_9.nsv", "result0835_10.nsv", "result0835_11.nsv", "result0835_12.nsv", "result0835_13.nsv", "result0835_14.nsv", "result0835_15.nsv", "result0835_16.nsv", "result0835_17.nsv", "result0835_18.nsv", "result0835_19.nsv", "result0835_20.nsv", "result0835_21.nsv", "result0835_22.nsv", "result0835_23.nsv", "result0835_24.nsv", "result0835_25.nsv", "result0835_26.nsv", "result0835_27.nsv", "result0835_28.nsv", "result0835_29.nsv", "result0835_30.nsv", "result0835_31.nsv", "result0835_32.nsv", "result0835_33.nsv", "result0835_34.nsv", "result0835_35.nsv", "result0835_36.nsv", "result0835_37.nsv", "result0835_38.nsv", "result0835_39.nsv", "result0835_40.nsv", "result0835_41.nsv", "result0835_42.nsv", "result0835_43.nsv", "result0835_44.nsv", "result0835_45.nsv", "result0835_46.nsv", "result0835_47.nsv", "result0835_48.nsv", "result0835_49.nsv", "result0835_50.nsv", "result0835_51.nsv", "result0835_52.nsv", "result0835_53.nsv", "result0835_54.nsv", "result0835_55.nsv", "result0835_56.nsv", "result0835_57.nsv"];
val thyn = "vfmTestDefs0835";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
