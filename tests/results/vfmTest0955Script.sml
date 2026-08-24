Theory vfmTest0955[no_sig_docs]
Ancestors vfmTestDefs0955
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0955_0.nsv", "result0955_1.nsv", "result0955_2.nsv", "result0955_3.nsv", "result0955_4.nsv", "result0955_5.nsv", "result0955_6.nsv", "result0955_7.nsv", "result0955_8.nsv", "result0955_9.nsv", "result0955_10.nsv", "result0955_11.nsv", "result0955_12.nsv", "result0955_13.nsv", "result0955_14.nsv", "result0955_15.nsv", "result0955_16.nsv", "result0955_17.nsv", "result0955_18.nsv", "result0955_19.nsv", "result0955_20.nsv", "result0955_21.nsv", "result0955_22.nsv", "result0955_23.nsv", "result0955_24.nsv", "result0955_25.nsv", "result0955_26.nsv", "result0955_27.nsv", "result0955_28.nsv", "result0955_29.nsv", "result0955_30.nsv", "result0955_31.nsv", "result0955_32.nsv", "result0955_33.nsv", "result0955_34.nsv", "result0955_35.nsv", "result0955_36.nsv", "result0955_37.nsv", "result0955_38.nsv", "result0955_39.nsv", "result0955_40.nsv", "result0955_41.nsv", "result0955_42.nsv", "result0955_43.nsv", "result0955_44.nsv", "result0955_45.nsv", "result0955_46.nsv", "result0955_47.nsv", "result0955_48.nsv", "result0955_49.nsv", "result0955_50.nsv", "result0955_51.nsv", "result0955_52.nsv", "result0955_53.nsv", "result0955_54.nsv"];
val thyn = "vfmTestDefs0955";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
