Theory vfmTest0069[no_sig_docs]
Ancestors vfmTestDefs0069
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0069_0.nsv", "result0069_1.nsv", "result0069_2.nsv", "result0069_3.nsv", "result0069_4.nsv", "result0069_5.nsv", "result0069_6.nsv", "result0069_7.nsv", "result0069_8.nsv", "result0069_9.nsv", "result0069_10.nsv", "result0069_11.nsv", "result0069_12.nsv", "result0069_13.nsv", "result0069_14.nsv", "result0069_15.nsv", "result0069_16.nsv", "result0069_17.nsv", "result0069_18.nsv", "result0069_19.nsv", "result0069_20.nsv", "result0069_21.nsv", "result0069_22.nsv", "result0069_23.nsv", "result0069_24.nsv", "result0069_25.nsv", "result0069_26.nsv", "result0069_27.nsv", "result0069_28.nsv", "result0069_29.nsv", "result0069_30.nsv", "result0069_31.nsv", "result0069_32.nsv", "result0069_33.nsv", "result0069_34.nsv", "result0069_35.nsv", "result0069_36.nsv", "result0069_37.nsv", "result0069_38.nsv", "result0069_39.nsv", "result0069_40.nsv", "result0069_41.nsv", "result0069_42.nsv", "result0069_43.nsv", "result0069_44.nsv", "result0069_45.nsv", "result0069_46.nsv", "result0069_47.nsv", "result0069_48.nsv", "result0069_49.nsv", "result0069_50.nsv", "result0069_51.nsv", "result0069_52.nsv", "result0069_53.nsv", "result0069_54.nsv", "result0069_55.nsv"];
val thyn = "vfmTestDefs0069";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
