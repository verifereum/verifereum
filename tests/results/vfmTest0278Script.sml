Theory vfmTest0278[no_sig_docs]
Ancestors vfmTestDefs0278
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0278_0.nsv", "result0278_1.nsv", "result0278_2.nsv", "result0278_3.nsv", "result0278_4.nsv", "result0278_5.nsv", "result0278_6.nsv", "result0278_7.nsv", "result0278_8.nsv", "result0278_9.nsv", "result0278_10.nsv", "result0278_11.nsv", "result0278_12.nsv", "result0278_13.nsv", "result0278_14.nsv", "result0278_15.nsv", "result0278_16.nsv", "result0278_17.nsv", "result0278_18.nsv", "result0278_19.nsv", "result0278_20.nsv", "result0278_21.nsv", "result0278_22.nsv", "result0278_23.nsv", "result0278_24.nsv", "result0278_25.nsv", "result0278_26.nsv", "result0278_27.nsv", "result0278_28.nsv", "result0278_29.nsv", "result0278_30.nsv", "result0278_31.nsv", "result0278_32.nsv", "result0278_33.nsv", "result0278_34.nsv", "result0278_35.nsv", "result0278_36.nsv", "result0278_37.nsv", "result0278_38.nsv", "result0278_39.nsv", "result0278_40.nsv", "result0278_41.nsv", "result0278_42.nsv", "result0278_43.nsv", "result0278_44.nsv", "result0278_45.nsv", "result0278_46.nsv", "result0278_47.nsv", "result0278_48.nsv", "result0278_49.nsv", "result0278_50.nsv", "result0278_51.nsv", "result0278_52.nsv", "result0278_53.nsv", "result0278_54.nsv", "result0278_55.nsv"];
val thyn = "vfmTestDefs0278";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
